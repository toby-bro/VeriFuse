package main

import (
	"fmt"
	"log"
	"os"
	"os/exec"
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

func compileIVerilog() error {
	cmd := exec.Command("iverilog", "-o", "ibex_sim_iv", "ibex_branch_predict.sv", "testbench.sv", "prim_assert.sv")
	return cmd.Run()
}

func compileVerilator() error {
	cmd := exec.Command("verilator", "--cc", "--exe", "--build", "ibex_branch_predict.sv", "testbench.cpp", "prim_assert.sv")
	return cmd.Run()
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

func main() {
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
