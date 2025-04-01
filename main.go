package main

import (
	"fmt"
	"log"
	"os"
	"os/exec"
	"regexp"
	"strings"
)

type TestCase struct {
	FetchRdata uint32
	FetchPc    uint32
	FetchValid uint8
}

type SimResult struct {
	BranchTaken uint8
	BranchPc    uint32
}

type EnumCast struct {
	Line       string
	EnumType   string
	Expression string
	DefaultVal string // Added field for default value
}

func compileIVerilog() error {
	cmd := exec.Command("iverilog", "-I../ibex", "-o", "ibex_sim_iv", "ibex_branch_predict_mocked.sv", "testbench.sv")
	return cmd.Run()
}

func compileVerilator() error {
	cmd := exec.Command("verilator", "--cc", "--exe", "--build", "ibex_branch_predict_mocked.sv", "testbench.cpp")
	return cmd.Run()
}

func detectEnumCasts() []EnumCast {
	// Read the SystemVerilog file
	content, err := os.ReadFile("ibex_branch_predict.sv")
	if err != nil {
		log.Fatal("Failed to read SystemVerilog file:", err)
	}

	// Regular expression to match enum casts
	// Matches patterns like: enum_type'(expression)
	enumCastRegex := regexp.MustCompile(`(\w+)'?\(([^)]+)\)`)

	var casts []EnumCast
	lines := strings.Split(string(content), "\n")

	for _, line := range lines {
		matches := enumCastRegex.FindAllStringSubmatch(line, -1)
		for _, match := range matches {
			if len(match) == 3 {
				cast := EnumCast{
					Line:       strings.TrimSpace(line),
					EnumType:   match[1],
					Expression: match[2],
					DefaultVal: getPlausibleValue(match[1]),
				}
				casts = append(casts, cast)
			}
		}
	}

	return casts
}

func getPlausibleValue(enumType string) string {
	// Common SystemVerilog enum types and their plausible values
	enumDefaults := map[string]string{
		"ibex_mubi_t":   "MuBi4True", // Common Ibex type
		"rv32b_e":       "RV32BNone", // RISC-V extension type
		"rv32m_e":       "RV32MFast", // RISC-V M extension type
		"opcode_e":      "2'b00",     // Generic opcode
		"branch_op_e":   "3'b000",    // Branch operation
		"alu_op_e":      "4'b0000",   // ALU operation
		"csr_op_e":      "2'b00",     // CSR operation
		"decoder_err_e": "1'b0",      // Decoder error flag
		"priv_lvl_e":    "2'b00",     // Privilege level
		"operation_e":   "1'b0",      // Generic operation
		"status_e":      "1'b0",      // Status indicator
	}

	if val, ok := enumDefaults[enumType]; ok {
		return val
	}

	// Default fallback values based on common patterns
	if strings.HasSuffix(enumType, "_e") {
		return "0" // Enums typically start at 0
	}
	if strings.HasSuffix(enumType, "_t") {
		return "1'b0" // Type suffixed enums, assume boolean
	}
	return "0" // Generic fallback
}

func mock_enum_cast(cast EnumCast) string {
	// If the expression is already a number, use it
	if regexp.MustCompile(`^[0-9]+('?[bdh][0-9a-fA-F_]+)?$`).MatchString(cast.Expression) {
		return cast.Expression
	}

	// Otherwise, provide a plausible value based on the enum type
	return getPlausibleValue(cast.EnumType)
}

func generateTestbench() error {
	// Create SystemVerilog testbench
	svTb := `
module testbench;
    logic clk_i;
    logic rst_ni;
    logic [31:0] fetch_rdata_i;
    logic [31:0] fetch_pc_i;
    logic        fetch_valid_i;
    logic        predict_branch_taken_o;
    logic [31:0] predict_branch_pc_o;

    ibex_branch_predict dut (.*);

    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, testbench);
        
        // Read inputs from stdin
        $readmemh("input.hex", fetch_rdata_i);
        $readmemh("pc.hex", fetch_pc_i);
        $readmemb("valid.hex", fetch_valid_i);

        #1;
        
        // Write outputs to files
        $writememb("taken.hex", predict_branch_taken_o);
        $writememh("target.hex", predict_branch_pc_o);
        
        $finish;
    end
endmodule`

	return os.WriteFile("testbench.sv", []byte(svTb), 0644)
}

func runTest(input TestCase) (SimResult, SimResult, error) {
	// Write input files
	writeHexFile("input.hex", input.FetchRdata)
	writeHexFile("pc.hex", input.FetchPc)
	writeBinFile("valid.hex", input.FetchValid)

	// Run iverilog simulation
	if err := exec.Command("./ibex_sim_iv").Run(); err != nil {
		return SimResult{}, SimResult{}, fmt.Errorf("iverilog sim failed: %v", err)
	}
	ivResult, err := readSimResults()
	if err != nil {
		return SimResult{}, SimResult{}, err
	}

	// Run verilator simulation
	if err := exec.Command("./obj_dir/Vibex_branch_predict").Run(); err != nil {
		return SimResult{}, SimResult{}, fmt.Errorf("verilator sim failed: %v", err)
	}
	vlResult, err := readSimResults()
	if err != nil {
		return SimResult{}, SimResult{}, err
	}

	return ivResult, vlResult, nil
}

func writeHexFile(filename string, data uint32) error {
	f, err := os.Create(filename)
	if err != nil {
		return err
	}
	defer f.Close()
	fmt.Fprintf(f, "%08x\n", data)
	return nil
}

func writeBinFile(filename string, data uint8) error {
	return os.WriteFile(filename, []byte{data}, 0644)
}

func readSimResults() (SimResult, error) {
	taken, err := os.ReadFile("taken.hex")
	if err != nil {
		return SimResult{}, err
	}

	target, err := os.ReadFile("target.hex")
	if err != nil {
		return SimResult{}, err
	}

	var result SimResult
	result.BranchTaken = taken[0] - '0'

	var targetVal uint32
	fmt.Sscanf(string(target), "%x", &targetVal)
	result.BranchPc = targetVal

	return result, nil
}

func readOriginalSV(filename string) (string, error) {
	content, err := os.ReadFile(filename)
	if err != nil {
		return "", fmt.Errorf("failed to read SV file: %v", err)
	}
	return string(content), nil
}

func replaceMockedEnumCasts(content string, casts []EnumCast) string {
	lines := strings.Split(content, "\n")
	for i, line := range lines {
		for _, cast := range casts {
			if strings.Contains(line, cast.Line) {
				originalCast := fmt.Sprintf("%s'(%s)", cast.EnumType, cast.Expression)
				mockedValue := mock_enum_cast(cast)
				lines[i] = strings.Replace(line, originalCast, mockedValue, 1)
			}
		}
	}
	return strings.Join(lines, "\n")
}

func writeMockedSV(content string) error {
	return os.WriteFile("ibex_branch_predict_mocked.sv", []byte(content), 0644)
}

func main() {
	// Read original SystemVerilog file
	originalContent, err := readOriginalSV("ibex_branch_predict.sv")
	if err != nil {
		log.Fatal(err)
	}

	// Detect and mock enum casts
	enumCasts := detectEnumCasts()
	if len(enumCasts) > 0 {
		log.Println("Detected enum casts and their mocked values:")
		for _, cast := range enumCasts {
			mockedValue := mock_enum_cast(cast)
			log.Printf("  Type: %s, Expression: %s -> Mocked: %s\n",
				cast.EnumType, cast.Expression, mockedValue)
		}

		// Create mocked version
		mockedContent := replaceMockedEnumCasts(originalContent, enumCasts)
		if err := writeMockedSV(mockedContent); err != nil {
			log.Fatal("Failed to write mocked SV file:", err)
		}
		log.Println("Created mocked SystemVerilog file: ibex_branch_predict_mocked.sv")
	}

	// Setup
	if err := generateTestbench(); err != nil {
		log.Fatal("Failed to generate testbench:", err)
	}

	if err := compileIVerilog(); err != nil {
		log.Fatal("Failed to compile with iverilog:", err)
	}

	if err := compileVerilator(); err != nil {
		log.Fatal("Failed to compile with verilator:", err)
	}

	// Fuzzing loop
	for i := 0; i < 1000; i++ {
		testCase := TestCase{
			FetchRdata: uint32(i), // You can make this more random
			FetchPc:    uint32(i * 4),
			FetchValid: 1,
		}

		ivResult, vlResult, err := runTest(testCase)
		if err != nil {
			log.Printf("Test %d failed: %v", i, err)
			continue
		}

		if ivResult != vlResult {
			log.Printf("Mismatch found in test %d:\n", i)
			log.Printf("  Input: rdata=%08x pc=%08x valid=%d\n",
				testCase.FetchRdata, testCase.FetchPc, testCase.FetchValid)
			log.Printf("  IVerilog: taken=%d pc=%08x\n",
				ivResult.BranchTaken, ivResult.BranchPc)
			log.Printf("  Verilator: taken=%d pc=%08x\n",
				vlResult.BranchTaken, vlResult.BranchPc)
		}
	}
}
