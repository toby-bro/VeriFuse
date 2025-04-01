package main

import (
	"bytes"
	"flag"
	"fmt"
	"log"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"time"
)

const TMP_DIR = "tmp_gen"

// Create temporary directory if it doesn't exist
func ensureTmpDir() error {
	if _, err := os.Stat(TMP_DIR); os.IsNotExist(err) {
		return os.MkdirAll(TMP_DIR, 0755)
	}
	return nil
}

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

// FuzzStats tracks statistics about the fuzzing run
type FuzzStats struct {
	TotalTests     int
	Mismatches     int
	SimErrors      int
	mutex          sync.Mutex
	FoundMutants   map[string]bool // Track unique mismatches
	LastMismatches []TestCase      // Store recent mismatches
}

func (fs *FuzzStats) addMismatch(tc TestCase) {
	fs.mutex.Lock()
	defer fs.mutex.Unlock()
	fs.Mismatches++

	// Create a unique key for this mismatch type
	key := fmt.Sprintf("R%x_P%x_V%d", tc.FetchRdata, tc.FetchPc, tc.FetchValid)

	// Track unique mismatches
	if !fs.FoundMutants[key] {
		fs.FoundMutants[key] = true

		// Keep last N mismatches for reporting
		if len(fs.LastMismatches) >= 5 {
			fs.LastMismatches = fs.LastMismatches[1:]
		}
		fs.LastMismatches = append(fs.LastMismatches, tc)
	}
}

func (fs *FuzzStats) addSimError() {
	fs.mutex.Lock()
	defer fs.mutex.Unlock()
	fs.SimErrors++
}

func (fs *FuzzStats) addTest() {
	fs.mutex.Lock()
	defer fs.mutex.Unlock()
	fs.TotalTests++
}

func (fs *FuzzStats) printSummary() {
	fmt.Printf("\n=== Fuzzing Summary ===\n")
	fmt.Printf("Total test cases: %d\n", fs.TotalTests)
	fmt.Printf("Simulator errors: %d\n", fs.SimErrors)
	fmt.Printf("Mismatches found: %d\n", fs.Mismatches)
	fmt.Printf("Unique mismatch types: %d\n", len(fs.FoundMutants))

	if len(fs.LastMismatches) > 0 {
		fmt.Printf("\nLast %d unique mismatches:\n", len(fs.LastMismatches))
		for i, tc := range fs.LastMismatches {
			fmt.Printf("%d: rdata=0x%08x, pc=0x%08x, valid=%d\n",
				i+1, tc.FetchRdata, tc.FetchPc, tc.FetchValid)
		}
	}
}

func compileIVerilog() error {
	cmd := exec.Command("iverilog", "-o", filepath.Join(TMP_DIR, "ibex_sim_iv"), "-g2012",
		filepath.Join(TMP_DIR, "ibex_branch_predict_mocked.sv"),
		filepath.Join(TMP_DIR, "testbench.sv"))
	return cmd.Run()
}

func compileVerilator() error {
	// Get absolute paths for clarity
	curDir, _ := os.Getwd()
	mockPath := filepath.Join(curDir, TMP_DIR, "ibex_branch_predict_mocked.sv")

	// Copy the file with proper module name
	content, err := os.ReadFile(mockPath)
	if err != nil {
		return fmt.Errorf("failed to read mocked file: %v", err)
	}

	// Replace module name in the content
	content = bytes.Replace(content,
		[]byte("module ibex_branch_predict"),
		[]byte("module ibex_branch_predict_mocked"), 1)

	if err := os.WriteFile(filepath.Join(curDir, TMP_DIR, "ibex_branch_predict_mocked.sv"), content, 0644); err != nil {
		return fmt.Errorf("failed to create module file: %v", err)
	}

	// Update testbench to use the correct header file name
	updateTestbenchCpp()

	// Change to the tmp_gen directory to run Verilator
	origDir, _ := os.Getwd()
	if err := os.Chdir(filepath.Join(curDir, TMP_DIR)); err != nil {
		return fmt.Errorf("failed to change directory: %v", err)
	}
	defer os.Chdir(origDir)

	// Run Verilator with the updated module name
	cmd := exec.Command("verilator", "--cc", "--exe", "--build", "-Mdir", "obj_dir",
		"ibex_branch_predict_mocked.sv", "testbench.cpp")

	var stderr bytes.Buffer
	cmd.Stderr = &stderr

	err = cmd.Run()
	if err != nil {
		log.Printf("Verilator error: %s\n%s", err, stderr.String())
	}

	return err
}

func updateTestbenchCpp() {
	// Read the testbench.cpp file
	content, err := os.ReadFile(filepath.Join(TMP_DIR, "testbench.cpp"))
	if err != nil {
		log.Printf("Warning: Could not read testbench.cpp: %v", err)
		return
	}

	// Replace the include statement and update file paths
	updatedContent := strings.ReplaceAll(
		string(content),
		"\"input.hex\"",
		"\""+filepath.Join(TMP_DIR, "input.hex")+"\"")

	updatedContent = strings.ReplaceAll(
		updatedContent,
		"\"pc.hex\"",
		"\""+filepath.Join(TMP_DIR, "pc.hex")+"\"")

	updatedContent = strings.ReplaceAll(
		updatedContent,
		"\"valid.hex\"",
		"\""+filepath.Join(TMP_DIR, "valid.hex")+"\"")

	updatedContent = strings.ReplaceAll(
		updatedContent,
		"\"taken.hex\"",
		"\""+filepath.Join(TMP_DIR, "taken.hex")+"\"")

	updatedContent = strings.ReplaceAll(
		updatedContent,
		"\"target.hex\"",
		"\""+filepath.Join(TMP_DIR, "target.hex")+"\"")

	// Write the updated content back
	if err := os.WriteFile(filepath.Join(TMP_DIR, "testbench.cpp"), []byte(updatedContent), 0644); err != nil {
		log.Printf("Warning: Could not update testbench.cpp: %v", err)
	}
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
	if strings.Contains(enumType, "opcode_e") {
		return "instr[6:0]"
	}

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
	// Generate SystemVerilog testbench with updated module name
	svTb := `// filepath: testbench.sv
module testbench;
    logic clk_i;
    logic rst_ni;
    logic [31:0] fetch_rdata_i;
    logic [31:0] fetch_pc_i;
    logic        fetch_valid_i;
    logic        predict_branch_taken_o;
    logic [31:0] predict_branch_pc_o;

    ibex_branch_predict_mocked dut (.*);

    initial begin
        string line;
        int fd;
        
        // Read inputs
        fd = $fopen("` + filepath.Join(TMP_DIR, "input.hex") + `", "r");
        $fgets(line, fd);
        $sscanf(line, "%h", fetch_rdata_i);
        $fclose(fd);
        
        fd = $fopen("` + filepath.Join(TMP_DIR, "pc.hex") + `", "r");
        $fgets(line, fd);
        $sscanf(line, "%h", fetch_pc_i);
        $fclose(fd);
        
        fd = $fopen("` + filepath.Join(TMP_DIR, "valid.hex") + `", "r");
        $fgets(line, fd);
        $sscanf(line, "%b", fetch_valid_i);
        $fclose(fd);

        #1;
        
        // Write outputs
        fd = $fopen("` + filepath.Join(TMP_DIR, "taken.hex") + `", "w");
        $fwrite(fd, "%0b", predict_branch_taken_o);
        $fclose(fd);
        
        fd = $fopen("` + filepath.Join(TMP_DIR, "target.hex") + `", "w");
        $fwrite(fd, "%h", predict_branch_pc_o);
        $fclose(fd);
        
        $finish;
    end
endmodule`

	if err := os.WriteFile(filepath.Join(TMP_DIR, "testbench.sv"), []byte(svTb), 0644); err != nil {
		return err
	}

	// Generate C++ testbench for Verilator
	cppTb := `// filepath: testbench.cpp
#include <verilated.h>
#include "Vibex_branch_predict_mocked.h"  // Updated header name
#include <fstream>
#include <iostream>
#include <cstdint>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Vibex_branch_predict_mocked* dut = new Vibex_branch_predict_mocked;  // Updated class name

    // Read input values
    std::ifstream input_file("` + filepath.Join(TMP_DIR, "input.hex") + `");
    std::ifstream pc_file("` + filepath.Join(TMP_DIR, "pc.hex") + `");
    std::ifstream valid_file("` + filepath.Join(TMP_DIR, "valid.hex") + `");
    
    uint32_t fetch_rdata, fetch_pc;
    uint8_t fetch_valid;
    
    input_file >> std::hex >> fetch_rdata;
    pc_file >> std::hex >> fetch_pc;
    valid_file >> fetch_valid;

    // Apply inputs
    dut->fetch_rdata_i = fetch_rdata;
    dut->fetch_pc_i = fetch_pc;
    dut->fetch_valid_i = fetch_valid;
    dut->clk_i = 0;
    dut->rst_ni = 1;

    // Evaluate
    dut->eval();

    // Write outputs
    std::ofstream taken_file("` + filepath.Join(TMP_DIR, "taken.hex") + `");
    std::ofstream target_file("` + filepath.Join(TMP_DIR, "target.hex") + `");
    
    taken_file << (int)dut->predict_branch_taken_o;
    target_file << std::hex << dut->predict_branch_pc_o;

    delete dut;
    return 0;
}`

	return os.WriteFile(filepath.Join(TMP_DIR, "testbench.cpp"), []byte(cppTb), 0644)
}

func runTest(input TestCase) (SimResult, SimResult, error) {
	writeHexFile(filepath.Join(TMP_DIR, "input.hex"), input.FetchRdata)
	writeHexFile(filepath.Join(TMP_DIR, "pc.hex"), input.FetchPc)
	writeBinFile(filepath.Join(TMP_DIR, "valid.hex"), input.FetchValid)

	if err := exec.Command(filepath.Join(TMP_DIR, "ibex_sim_iv")).Run(); err != nil {
		return SimResult{}, SimResult{}, fmt.Errorf("iverilog sim failed: %v", err)
	}
	ivResult, err := readSimResults()
	if err != nil {
		return SimResult{}, SimResult{}, err
	}

	if err := exec.Command(filepath.Join(TMP_DIR, "obj_dir", "Vibex_branch_predict_mocked")).Run(); err != nil {
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
	taken, err := os.ReadFile(filepath.Join(TMP_DIR, "taken.hex"))
	if err != nil {
		return SimResult{}, err
	}

	target, err := os.ReadFile(filepath.Join(TMP_DIR, "target.hex"))
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
	// Rename the module
	moduleRegex := regexp.MustCompile(`module\s+(\w+)\s*\(`)
	content = moduleRegex.ReplaceAllString(content, "module ${1}_mocked (")

	return os.WriteFile(filepath.Join(TMP_DIR, "ibex_branch_predict_mocked.sv"), []byte(content), 0644)
}

func detectMacros(content string) []string {
	var macros []string
	// Match macro invocations starting with ` or $ and include statements
	macroRegex := regexp.MustCompile("(`|\\$)\\w+|`include\\s+\"[^\"]+\"")

	matches := macroRegex.FindAllString(content, -1)
	for _, match := range matches {
		macros = append(macros, match)
	}

	return macros
}

func removeMacros(content string, macros []string) string {
	lines := strings.Split(content, "\n")
	var result []string

	for _, line := range lines {
		shouldKeep := true
		for _, macro := range macros {
			if strings.Contains(line, macro) {
				shouldKeep = false
				break
			}
		}
		if shouldKeep {
			result = append(result, line)
		}
	}

	return strings.Join(result, "\n")
}

func removeUniqueCases(content string) string {
	lines := strings.Split(content, "\n")
	for i, line := range lines {
		if strings.Contains(line, "unique case") {
			lines[i] = strings.Replace(line, "unique case", "case", 1)
		}
	}
	return strings.Join(lines, "\n")
}

// removeComments removes all comments from SystemVerilog code
func removeComments(content string) string {
	// First, remove single-line comments
	singleLineCommentRegex := regexp.MustCompile(`//.*$`)
	lines := strings.Split(content, "\n")
	for i, line := range lines {
		lines[i] = singleLineCommentRegex.ReplaceAllString(line, "")
	}
	content = strings.Join(lines, "\n")

	// Then, remove multi-line comments
	multiLineCommentRegex := regexp.MustCompile(`/\*[\s\S]*?\*/`)
	content = multiLineCommentRegex.ReplaceAllString(content, "")

	// Clean up any empty lines
	emptyLineRegex := regexp.MustCompile(`\n\s*\n`)
	for emptyLineRegex.MatchString(content) {
		content = emptyLineRegex.ReplaceAllString(content, "\n")
	}

	return content
}

// generateRandomInput creates a random test case based on fuzzing strategy
func generateRandomInput(strategy string, seed int64, iteration int) TestCase {
	r := rand.New(rand.NewSource(seed + int64(iteration)))

	var testCase TestCase

	switch strategy {
	case "simple":
		// Basic random values
		testCase.FetchRdata = uint32(r.Uint32())
		testCase.FetchPc = uint32(r.Uint32())
		testCase.FetchValid = uint8(r.Intn(2)) // 0 or 1

	case "opcode-aware":
		// Generate random opcodes that make sense for branch prediction
		opcodes := []uint32{
			0x63, // BRANCH opcode (0x63)
			0x6F, // JAL opcode (0x6F)
			0x01, // Compressed instruction
			0x00, // Random other
		}

		// Pick an opcode type
		opcodeType := r.Intn(len(opcodes))
		baseInstr := uint32(0)

		switch opcodes[opcodeType] {
		case 0x63: // BRANCH
			// Build a BRANCH instruction with random fields
			imm := uint32(r.Intn(4096) - 2048) // Some random immediate
			rs1 := uint32(r.Intn(32))          // Source register
			rs2 := uint32(r.Intn(32))          // Source register
			funct3 := uint32(r.Intn(8))        // Branch type

			// Pack the fields into instruction format
			imm12_10_5 := (imm >> 5) & 0x7F
			imm4_1_11 := ((imm & 0x1E) | ((imm >> 11) & 0x1))

			baseInstr = (((imm >> 12) & 0x1) << 31) | // imm[12]
				(imm12_10_5 << 25) | // imm[10:5]
				(rs2 << 20) | // rs2
				(rs1 << 15) | // rs1
				(funct3 << 12) | // funct3
				(imm4_1_11 << 8) | // imm[4:1,11]
				0x63 // BRANCH opcode

		case 0x6F: // JAL
			// Build a JAL instruction
			imm := uint32(r.Intn(1048576) - 524288) // Some random immediate
			rd := uint32(r.Intn(32))                // Destination register

			// Pack fields into instruction format
			baseInstr = (((imm >> 20) & 0x1) << 31) | // imm[20]
				(((imm >> 1) & 0x3FF) << 21) | // imm[10:1]
				(((imm >> 11) & 0x1) << 20) | // imm[11]
				(((imm >> 12) & 0xFF) << 12) | // imm[19:12]
				(rd << 7) | // rd
				0x6F // JAL opcode

		case 0x01: // Compressed instruction
			// Construct a valid compressed branch or jump
			isJump := r.Intn(2) == 1
			if isJump {
				// C.J or C.JAL format
				baseInstr = (uint32(r.Intn(2)) << 15) | // Choose between C.J and C.JAL
					(uint32(3) << 13) | // funct3 = 3 for C.JAL, 1 for C.J
					(uint32(r.Intn(2048)) << 2) | // Random immediate
					0x01 // Compressed instruction marker
			} else {
				// C.BEQZ or C.BNEZ
				baseInstr = (uint32(r.Intn(2)+6) << 13) | // 6 for C.BEQZ, 7 for C.BNEZ
					(uint32(r.Intn(8)) << 10) | // Register rs1'
					(uint32(r.Intn(256)) << 2) | // Immediate
					0x01 // Compressed instruction marker
			}

		default: // Random instruction
			baseInstr = r.Uint32()
		}

		testCase.FetchRdata = baseInstr
		testCase.FetchPc = uint32(r.Intn(1048576)) * 4 // Align to 4-byte boundary
		testCase.FetchValid = 1

	case "mutation":
		// Start with previous interesting cases and mutate them
		if iteration > 0 && len(stats.LastMismatches) > 0 {
			// Select a previous mismatch to mutate
			baseCase := stats.LastMismatches[r.Intn(len(stats.LastMismatches))]
			testCase = baseCase

			// Apply random mutations
			switch r.Intn(4) {
			case 0:
				// Flip random bits in the instruction
				numBits := r.Intn(5) + 1
				for i := 0; i < numBits; i++ {
					bitPos := r.Intn(32)
					testCase.FetchRdata ^= (1 << bitPos)
				}
			case 1:
				// Modify the PC value
				testCase.FetchPc = baseCase.FetchPc + uint32(r.Intn(16)-8)*4
			case 2:
				// Toggle valid flag
				testCase.FetchValid = 1 - baseCase.FetchValid
			case 3:
				// Create edge case by focusing on specific bits
				// that might affect branch prediction logic
				opcodeField := testCase.FetchRdata & 0x7F
				// Keep opcode, randomize other fields
				testCase.FetchRdata = (r.Uint32() & 0xFFFFFF80) | opcodeField
			}
		} else {
			// Fall back to simple random if no interesting cases yet
			testCase.FetchRdata = uint32(r.Uint32())
			testCase.FetchPc = uint32(r.Uint32() & 0xFFFFFFFC) // Word-aligned
			testCase.FetchValid = uint8(r.Intn(2))
		}

	default: // Fallback to truly random
		testCase.FetchRdata = uint32(r.Uint32())
		testCase.FetchPc = uint32(r.Uint32())
		testCase.FetchValid = uint8(r.Intn(2))
	}

	return testCase
}

var stats FuzzStats

func main() {
	// Parse command-line flags
	numTests := flag.Int("n", 1000, "Number of test cases to run")
	strategy := flag.String("strategy", "opcode-aware", "Fuzzing strategy: simple, opcode-aware, mutation")
	workers := flag.Int("workers", runtime.NumCPU(), "Number of parallel workers")
	seedFlag := flag.Int64("seed", time.Now().UnixNano(), "Random seed")
	verbose := flag.Bool("v", false, "Verbose output")
	flag.Parse()

	// Initialize stats
	stats = FuzzStats{
		FoundMutants:   make(map[string]bool),
		LastMismatches: make([]TestCase, 0),
	}

	// Ensure tmp_gen directory exists
	if err := ensureTmpDir(); err != nil {
		log.Fatal("Failed to create temporary directory:", err)
	}

	// Setup phase
	originalContent, err := readOriginalSV("ibex_branch_predict.sv")
	if err != nil {
		log.Fatal(err)
	}

	// Remove unique from case statements
	originalContent = removeUniqueCases(originalContent)

	// Detect macros first
	macros := detectMacros(originalContent)
	if len(macros) > 0 {
		log.Println("Detected macros that will be removed:")
		for _, macro := range macros {
			log.Printf("  %s\n", macro)
		}
		// Remove macros from content
		originalContent = removeMacros(originalContent, macros)
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

	// Remove comments from the mocked content
	//mockedContent = removeComments(mockedContent)

	// Now write to tmp_gen directory
	if err := writeMockedSV(mockedContent); err != nil {
		log.Fatal("Failed to write mocked SV file:", err)
	}
	log.Printf("Created mocked SystemVerilog file: %s", filepath.Join(TMP_DIR, "ibex_branch_predict_mocked.sv"))

	// Generate testbenches FIRST
	if err := generateTestbench(); err != nil {
		log.Fatal("Failed to generate testbenches:", err)
	}
	log.Printf("Created testbenches in %s directory", TMP_DIR)

	// THEN compile them
	if err := compileIVerilog(); err != nil {
		log.Fatal("Failed to compile with iverilog:", err)
	}
	log.Println("Successfully compiled with iverilog")

	if err := compileVerilator(); err != nil {
		log.Fatal("Failed to compile with verilator:", err)
	}
	log.Println("Successfully compiled with verilator")

	log.Printf("Starting fuzzing with %d test cases using strategy: %s\n", *numTests, *strategy)

	// Create a worker pool for parallel fuzzing
	var wg sync.WaitGroup
	testCases := make(chan int, *workers)

	// Progress tracking
	ticker := time.NewTicker(5 * time.Second)
	done := make(chan struct{})

	go func() {
		for {
			select {
			case <-ticker.C:
				log.Printf("Progress: %d/%d tests run, %d mismatches found\n",
					stats.TotalTests, *numTests, stats.Mismatches)
			case <-done:
				ticker.Stop()
				return
			}
		}
	}()

	// Start worker goroutines
	for w := 0; w < *workers; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for i := range testCases {
				testCase := generateRandomInput(*strategy, *seedFlag, i)
				stats.addTest()

				ivResult, vlResult, err := runTest(testCase)
				if err != nil {
					if *verbose {
						log.Printf("Test %d failed: %v", i, err)
					}
					stats.addSimError()
					continue
				}

				if ivResult != vlResult {
					log.Printf("Mismatch found in test %d:\n", i)
					log.Printf("  Input: rdata=0x%08x pc=0x%08x valid=%d\n",
						testCase.FetchRdata, testCase.FetchPc, testCase.FetchValid)
					log.Printf("  IVerilog: taken=%d pc=0x%08x\n",
						ivResult.BranchTaken, ivResult.BranchPc)
					log.Printf("  Verilator: taken=%d pc=0x%08x\n",
						vlResult.BranchTaken, vlResult.BranchPc)

					stats.addMismatch(testCase)

					// Save testcase to file for reproduction
					filename := fmt.Sprintf("mismatch_%d.txt", i)
					f, err := os.Create(filename)
					if err == nil {
						fmt.Fprintf(f, "rdata=0x%08x\npc=0x%08x\nvalid=%d\n",
							testCase.FetchRdata, testCase.FetchPc, testCase.FetchValid)
						f.Close()
						log.Printf("  Saved to %s for reproduction\n", filename)
					}
				}
			}
		}()
	}

	// Feed test cases to workers
	for i := 0; i < *numTests; i++ {
		testCases <- i
	}
	close(testCases)

	// Wait for all workers to finish
	wg.Wait()
	done <- struct{}{}

	// Print summary
	stats.printSummary()

	if stats.Mismatches > 0 {
		log.Printf("Found %d mismatches between iverilog and verilator!\n", stats.Mismatches)
		os.Exit(1)
	} else {
		log.Printf("No mismatches found after %d tests.\n", *numTests)
	}
}
