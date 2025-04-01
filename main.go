package main

import (
	"fmt"
	"log"
	"math/rand"
	"os"
	"os/exec"
	"regexp"
	"strconv"
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
	DefaultVal string
}

type UndefinedIdentifier struct {
	Line    string
	Name    string
	Context string
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
	content, err := os.ReadFile("ibex_branch_predict.sv")
	if err != nil {
		log.Fatal("Failed to read SystemVerilog file:", err)
	}

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

func detectUndefinedIdentifiers() []UndefinedIdentifier {
	content, err := os.ReadFile("ibex_branch_predict.sv")
	if err != nil {
		log.Fatal("Failed to read SystemVerilog file:", err)
	}

	knownKeywords := map[string]bool{
		"module": true, "input": true, "output": true, "logic": true,
		"always_comb": true, "assign": true, "begin": true, "end": true,
		"if": true, "else": true, "case": true, "endcase": true,
		"unique": true, "default": true, "parameter": true,
	}

	var undefinedVars []UndefinedIdentifier
	lines := strings.Split(string(content), "\n")

	identifierRegex := regexp.MustCompile(`\b([A-Za-z_][A-Za-z0-9_]*)\b`)

	for _, line := range lines {
		if strings.Contains(line, "//") || strings.Contains(line, "/*") {
			continue
		}

		matches := identifierRegex.FindAllStringSubmatch(line, -1)
		for _, match := range matches {
			identifier := match[1]
			if !knownKeywords[identifier] && strings.Contains(line, identifier) {
				if strings.HasSuffix(identifier, "_e") || strings.HasSuffix(identifier, "_t") ||
					strings.HasPrefix(identifier, "OPCODE_") {
					undefinedVars = append(undefinedVars, UndefinedIdentifier{
						Line:    strings.TrimSpace(line),
						Name:    identifier,
						Context: inferContext(line),
					})
				}
			}
		}
	}

	return undefinedVars
}

func inferContext(line string) string {
	if strings.Contains(line, "opcode_e") {
		return "opcode"
	} else if strings.Contains(line, "assign") {
		return "signal"
	} else if strings.Contains(line, "parameter") {
		return "parameter"
	}
	return "unknown"
}

func generateRandomBitString(width int) string {
	val := rand.Uint64() & ((1 << width) - 1)
	return fmt.Sprintf("%d'b%b", width, val)
}

func generateRandomHexString(width int) string {
	bytes := (width + 3) / 4
	val := rand.Uint64() & ((1 << (bytes * 4)) - 1)
	return fmt.Sprintf("%d'h%x", width, val)
}

func inferBitWidth(context string) int {
	if match := regexp.MustCompile(`\[(\d+):0\]`).FindStringSubmatch(context); match != nil {
		if width, err := strconv.Atoi(match[1]); err == nil {
			return width + 1
		}
	}

	switch {
	case strings.Contains(context, "opcode"):
		return 7
	case strings.Contains(context, "branch"):
		return 3
	default:
		return rand.Intn(32) + 1
	}
}

func getPlausibleValue(enumType string) string {
	width := inferBitWidth("")

	switch {
	case strings.HasSuffix(enumType, "_e"):
		return fmt.Sprintf("%d", rand.Intn(8))
	case strings.HasSuffix(enumType, "_t"):
		return generateRandomBitString(width)
	default:
		if rand.Float32() < 0.5 {
			return generateRandomBitString(width)
		}
		return generateRandomHexString(width)
	}
}

func mockIdentifier(id UndefinedIdentifier) string {
	width := inferBitWidth(id.Context)

	switch {
	case strings.HasPrefix(id.Name, "OPCODE_"):
		return generateRandomBitString(7)
	case strings.Contains(id.Context, "enum"):
		return fmt.Sprintf("%d", rand.Intn(8))
	case strings.Contains(id.Context, "logic"):
		return generateRandomBitString(width)
	default:
		if rand.Float32() < 0.5 {
			return generateRandomBitString(width)
		}
		return generateRandomHexString(width)
	}
}

func mock_enum_cast(cast EnumCast) string {
	if regexp.MustCompile(`^[0-9]+('?[bdh][0-9a-fA-F_]+)?$`).MatchString(cast.Expression) {
		return cast.Expression
	}

	return getPlausibleValue(cast.EnumType)
}

func generateTestbench() error {
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
        
        $readmemh("input.hex", fetch_rdata_i);
        $readmemh("pc.hex", fetch_pc_i);
        $readmemb("valid.hex", fetch_valid_i);

        #1;
        
        $writememb("taken.hex", predict_branch_taken_o);
        $writememh("target.hex", predict_branch_pc_o);
        
        $finish;
    end
endmodule`

	return os.WriteFile("testbench.sv", []byte(svTb), 0644)
}

func runTest(input TestCase) (SimResult, SimResult, error) {
	writeHexFile("input.hex", input.FetchRdata)
	writeHexFile("pc.hex", input.FetchPc)
	writeBinFile("valid.hex", input.FetchValid)

	if err := exec.Command("./ibex_sim_iv").Run(); err != nil {
		return SimResult{}, SimResult{}, fmt.Errorf("iverilog sim failed: %v", err)
	}
	ivResult, err := readSimResults()
	if err != nil {
		return SimResult{}, SimResult{}, err
	}

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
	originalContent, err := readOriginalSV("ibex_branch_predict.sv")
	if err != nil {
		log.Fatal(err)
	}

	enumCasts := detectEnumCasts()
	if len(enumCasts) > 0 {
		log.Println("Detected enum casts and their mocked values:")
		for _, cast := range enumCasts {
			mockedValue := mock_enum_cast(cast)
			log.Printf("  Type: %s, Expression: %s -> Mocked: %s\n",
				cast.EnumType, cast.Expression, mockedValue)
		}
	}

	undefinedVars := detectUndefinedIdentifiers()
	if len(undefinedVars) > 0 {
		log.Println("Detected undefined identifiers and their mocked values:")
		for _, undef := range undefinedVars {
			mockedValue := mockIdentifier(undef)
			log.Printf("  Name: %s, Context: %s -> Mocked: %s\n",
				undef.Name, undef.Context, mockedValue)
		}
	}

	mockedContent := replaceMockedEnumCasts(originalContent, enumCasts)
	for _, undef := range undefinedVars {
		mockedContent = strings.Replace(mockedContent, undef.Name,
			mockIdentifier(undef), -1)
	}

	if err := writeMockedSV(mockedContent); err != nil {
		log.Fatal("Failed to write mocked SV file:", err)
	}
	log.Println("Created mocked SystemVerilog file: ibex_branch_predict_mocked.sv")

	if err := generateTestbench(); err != nil {
		log.Fatal("Failed to generate testbench:", err)
	}

	if err := compileIVerilog(); err != nil {
		log.Fatal("Failed to compile with iverilog:", err)
	}

	if err := compileVerilator(); err != nil {
		log.Fatal("Failed to compile with verilator:", err)
	}

	for i := 0; i < 1000; i++ {
		testCase := TestCase{
			FetchRdata: uint32(i),
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
