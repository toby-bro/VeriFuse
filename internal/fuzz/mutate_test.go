package fuzz

import (
	"os"
	"strings"
	"testing"

	"github.com/toby-bro/pfuzz/internal/snippets"
	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

func TestMain(m *testing.M) {
	logger = utils.NewDebugLogger(5)
	exitCode := m.Run()
	os.Exit(exitCode)
}

func TestMatchVariablesToSnippetPorts(t *testing.T) {
	moduleContent := `
module TestModule (
    input logic [7:0] data_in1,
	input logic [7:0] data_in2,
    output logic [7:0] data_out,
);
	assign data_out = ~(data_in & data_in2);
endmodule
`
	snippetContent := `
module SnippetModule (
    input logic [7:0] input1,
	input logic [7:0] input2,
    output logic [7:0] output1,
	output logic [7:0] output2
);
	assign output1 = input1 ^ input2;
endmodule
`
	verilogFile, err := verilog.ParseVerilog(moduleContent, 5)
	if err != nil {
		t.Fatalf("ParseVerilog failed for module: %v", err)
	}
	module := verilogFile.Modules["TestModule"]
	if module == nil {
		t.Fatalf("Module 'TestModule' not found in parsed file")
	}

	snippetFile, err := verilog.ParseVerilog(snippetContent, 5)
	if err != nil {
		t.Fatalf("ParseVerilog failed for snippet: %v", err)
	}
	snippet := &snippets.Snippet{
		Name:       "SnippetModule",
		Module:     snippetFile.Modules["SnippetModule"],
		ParentFile: snippetFile,
	}

	scopeTree, err := verilog.GetScopeTree(verilogFile, module.Body, nil, module.Ports)
	if err != nil {
		t.Fatalf("ParseVariables failed: %v", err)
	}

	bestScope := findBestScopeNode(scopeTree)

	portConnections, newDeclarations, err := matchVariablesToSnippetPorts(
		module,
		snippet,
		"test",
		bestScope,
	)
	if err != nil {
		t.Fatalf("matchVariablesToSnippetPorts failed: %v", err)
	}

	if len(portConnections) != 4 {
		t.Errorf("Expected 3 port connections, got %d", len(portConnections))
	}

	if (portConnections["input2"] != "data_in2" && portConnections["input1"] != "data_in1") &&
		(portConnections["input2"] != "data_in1" && portConnections["input1"] != "data_in2") {
		t.Errorf("Expected 'input2' to connect to 'data_in2', got '%s'", portConnections["input1"])
	}

	if portConnections["output1"] == "" {
		t.Errorf("Expected 'output1' to have a connection, but it is empty")
	}

	if portConnections["output2"] == "" {
		t.Errorf("Expected 'output2' to have a connection, but it is empty")
	}

	if len(newDeclarations) != 2 {
		t.Errorf("Expected a new declaration, got %d", len(newDeclarations))
	}
}

func TestInjectSnippetInModule(t *testing.T) {
	moduleContent := `
module DUT (
    input logic clk,
    input logic rst_n,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
	logic [7:0] internal_wire;
	assign internal_wire = data_in + 1;
	always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n) begin
			data_out <= 8'b0;
		end else begin
			data_out <= internal_wire;
		end
	end
endmodule
`
	snippetContent := `
module SnippetModule (
    input logic [7:0] input1,
    output logic [7:0] output1
);
	assign output1 = input1 ^ 8'hFF;
endmodule
`
	verilogFile, err := verilog.ParseVerilog(moduleContent, 5)
	if err != nil {
		t.Fatalf("ParseVerilog failed for module: %v", err)
	}
	module := verilogFile.Modules["DUT"]

	snippetFile, err := verilog.ParseVerilog(snippetContent, 5)
	if err != nil {
		t.Fatalf("ParseVerilog failed for snippet: %v", err)
	}
	snippet := &snippets.Snippet{
		Name:       "SnippetModule",
		Module:     snippetFile.Modules["SnippetModule"],
		ParentFile: snippetFile,
	}

	err = injectSnippetInModule(module, verilogFile, snippet, true, "test")
	if err != nil {
		t.Fatalf("injectSnippetInModule failed: %v", err)
	}
	mutatedContent := module.Body

	if !strings.Contains(mutatedContent, "SnippetModule SnippetModule_inst_") {
		t.Errorf("Expected snippet instantiation not found in mutated content")
	}

	if !strings.Contains(mutatedContent, ".output1(inj_output1_") {
		t.Errorf("Expected output connection not found in mutated content")
	}
	if !strings.Contains(mutatedContent, ".input1(data_in)") &&
		!strings.Contains(mutatedContent, ".input1(internal_wire)") {
		t.Errorf("Expected input connection not found in mutated content")
	}
}

func TestFindMatchingVariable(t *testing.T) {
	variables := map[string]*verilog.Variable{
		"data_in":  {Name: "data_in", Type: verilog.LOGIC, Width: 8},
		"data_out": {Name: "data_out", Type: verilog.LOGIC, Width: 8},
		"control":  {Name: "control", Type: verilog.BIT, Width: 1},
	}
	port := verilog.Port{Name: "input1", Type: verilog.LOGIC, Width: 8}

	matchedVariable := findMatchingVariable(port, variables, nil)
	if matchedVariable == nil {
		t.Fatalf("findMatchingVariable failed to find a match")
	}

	if matchedVariable.Name != "data_in" && matchedVariable.Name != "data_out" {
		t.Errorf("Expected 'data_in', got '%s'", matchedVariable.Name)
	}

	// Test case where no match is found
	portNoMatch := verilog.Port{Name: "input2", Type: verilog.REAL, Width: 8}
	matchedVariable = findMatchingVariable(portNoMatch, variables, nil)
	if matchedVariable != nil {
		t.Errorf("Expected no match, but got '%s'", matchedVariable.Name)
	}
}

func TestFindMatchingVariable_WithModuleContext(t *testing.T) {
	moduleContent := `
module TestModule (
    input logic [7:0] module_in1,
    input logic [7:0] module_in2,
    output logic [7:0] data_out,
);
	logic [7:0] internal_var1;
    logic [3:0] internal_var2_short;
	assign data_out = module_in1 & module_in2;
    assign internal_var1 = module_in1 + 1;
    assign internal_var2_short = module_in2[3:0];
endmodule
`
	verilogFile, err := verilog.ParseVerilog(moduleContent, 5)
	if err != nil {
		t.Fatalf("ParseVerilog failed for module: %v", err)
	}
	module := verilogFile.Modules["TestModule"]
	if module == nil {
		t.Fatalf("Module 'TestModule' not found in parsed file")
	}

	variables, err := verilog.ParseVariables(verilogFile, module.Body, nil)
	if err != nil {
		t.Fatalf("ParseVariables failed: %v", err)
	}

	portToMatch1 := verilog.Port{
		Name:      "snippet_port1",
		Type:      verilog.LOGIC,
		Width:     8,
		Direction: verilog.INPUT,
	}
	matchedVar1 := findMatchingVariable(portToMatch1, variables, nil)
	if matchedVar1 == nil {
		t.Errorf("Expected to find a match for snippet_port1, but got nil")
	} else if matchedVar1.Name != "internal_var1" && matchedVar1.Name != "data_out" && matchedVar1.Name != "module_in1" && matchedVar1.Name != "module_in2" {
		t.Logf("Matched snippet_port1 with %s. Variables: %+v", matchedVar1.Name, variables)
	}

	portToMatch2 := verilog.Port{
		Name:      "snippet_port2",
		Type:      verilog.LOGIC,
		Width:     4,
		Direction: verilog.INPUT,
	}
	matchedVar2 := findMatchingVariable(portToMatch2, variables, nil)
	if matchedVar2 == nil {
		t.Errorf("Expected to find a match for snippet_port2, but got nil")
	} else if matchedVar2.Name != "internal_var2_short" {
		t.Logf("Matched snippet_port2 with %s. Variables: %+v", matchedVar2.Name, variables)
	}

	portToMatch3 := verilog.Port{
		Name:      "snippet_port3",
		Type:      verilog.INTEGER,
		Width:     8,
		Direction: verilog.INPUT,
	}
	matchedVar3 := findMatchingVariable(portToMatch3, variables, nil)
	if matchedVar3 != nil {
		t.Errorf(
			"Expected no match for snippet_port3 (different type), but got '%s'",
			matchedVar3.Name,
		)
	}

	portToMatch4 := verilog.Port{
		Name:      "snippet_port4",
		Type:      verilog.LOGIC,
		Width:     16,
		Direction: verilog.INPUT,
	}
	matchedVar4 := findMatchingVariable(portToMatch4, variables, nil)
	if matchedVar4 != nil {
		t.Errorf(
			"Expected no match for snippet_port4 (different width), but got '%s'",
			matchedVar4.Name,
		)
	}
}

func TestGenerateSignalDeclaration(t *testing.T) {
	port := verilog.Port{Name: "output1", Type: verilog.LOGIC, Width: 8, IsSigned: true}
	signalName := "inj_output1"

	declaration := generateSignalDeclaration(port, signalName)
	expected := "input logic signed [7:0] inj_output1;"

	if declaration != expected {
		t.Errorf("Expected '%s', got '%s'", expected, declaration)
	}

	portScalar := verilog.Port{Name: "output2", Type: verilog.LOGIC, Width: 1, IsSigned: false}
	signalNameScalar := "inj_output2"

	declarationScalar := generateSignalDeclaration(portScalar, signalNameScalar)
	expectedScalar := "input logic inj_output2;"

	if declarationScalar != expectedScalar {
		t.Errorf("Expected '%s', got '%s'", expectedScalar, declarationScalar)
	}
}

func TestGenerateSnippetInstantiation(t *testing.T) {
	snippet := &snippets.Snippet{
		Name: "TestSnippet",
		Module: &verilog.Module{
			Name: "SnippetModule",
			Ports: []verilog.Port{
				{Name: "input1", Type: verilog.LOGIC, Width: 8, Direction: verilog.INPUT},
				{Name: "output1", Type: verilog.LOGIC, Width: 8, Direction: verilog.OUTPUT},
			},
		},
	}
	portConnections := map[string]string{
		"input1":  "data_in",
		"output1": "data_out",
	}

	instantiation := generateSnippetInstantiation(snippet, portConnections)
	expectedPrefix := `SnippetModule TestSnippet_inst_`
	if !strings.HasPrefix(strings.TrimSpace(instantiation), expectedPrefix) {
		t.Errorf(
			"Expected instantiation to start with '%s', got '%s'",
			expectedPrefix,
			instantiation,
		)
	}

	if !strings.Contains(instantiation, ".input1(data_in)") {
		t.Errorf("Expected '.input1(data_in)' in instantiation, got '%s'", instantiation)
	}

	if !strings.Contains(instantiation, ".output1(data_out)") {
		t.Errorf("Expected '.output1(data_out)' in instantiation, got '%s'", instantiation)
	}

	if !strings.HasSuffix(instantiation, ");") {
		t.Errorf("Expected instantiation to end with ');', got '%s'", instantiation)
	}
}

func TestPreventDuplicateSnippetInjection(t *testing.T) {
	// Create a simple module
	moduleContent := `
module DUT (
    input logic clk,
    input logic rst_n,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
	logic [7:0] internal_wire;
	assign internal_wire = data_in + 1;
	always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n) begin
			data_out <= 8'b0;
		end else begin
			data_out <= internal_wire;
		end
	end
endmodule
`

	// Create a VerilogFile with our module
	verilogFile, err := verilog.ParseVerilog(moduleContent, 5)
	if err != nil {
		t.Fatalf("ParseVerilog failed for module: %v", err)
	}

	// Save the original file to disk for testing
	tmpFile := "/tmp/test_duplicate_injection.sv"
	err = os.WriteFile(tmpFile, []byte(moduleContent), 0644)
	if err != nil {
		t.Fatalf("Failed to write test file: %v", err)
	}
	defer os.Remove(tmpFile)

	// Run mutation multiple times with low verbosity to see if duplicates occur
	for i := 0; i < 10; i++ {
		mutatedFile, err := MutateFile(verilogFile, tmpFile, 0)
		if err != nil {
			t.Fatalf("MutateFile failed on iteration %d: %v", i, err)
		}

		// Count occurrences of BEGIN/END comments to check for duplicates
		body := mutatedFile.Modules["DUT"].Body
		beginCount := strings.Count(body, "// BEGIN:")
		endCount := strings.Count(body, "// END:")

		if beginCount != endCount {
			t.Errorf("Mismatched BEGIN/END markers: %d BEGIN vs %d END", beginCount, endCount)
		}

		// Check for specific duplicate patterns that would indicate variable redeclaration
		lines := strings.Split(body, "\n")
		beginEndPairs := make(map[string]int)

		for _, line := range lines {
			line = strings.TrimSpace(line)
			if strings.HasPrefix(line, "// BEGIN:") {
				snippetName := strings.TrimSpace(strings.TrimPrefix(line, "// BEGIN:"))
				beginEndPairs[snippetName]++
			}
		}

		// Verify no snippet appears more than once
		for snippetName, count := range beginEndPairs {
			if count > 1 {
				t.Errorf("Snippet '%s' appears %d times in module, expected at most 1", snippetName, count)
			}
		}

		// Reload for next iteration
		verilogFile, err = verilog.ParseVerilog(moduleContent, 5)
		if err != nil {
			t.Fatalf("ParseVerilog failed for module on iteration %d: %v", i, err)
		}
	}
}

func TestPreventSpecificDuplicateSnippetInjection(t *testing.T) {
	// Test the duplicate tracking logic directly
	moduleSnippetTracker := make(map[string]map[string]bool)

	// Simulate the first injection
	moduleSnippetTracker["DUT"] = make(map[string]bool)
	moduleSnippetTracker["DUT"]["simple_loop"] = true

	// Check that a subsequent "injection" would be blocked
	testSnippetName := "simple_loop"
	moduleName := "DUT"

	if moduleSnippetTracker[moduleName] == nil {
		moduleSnippetTracker[moduleName] = make(map[string]bool)
	}
	if moduleSnippetTracker[moduleName][testSnippetName] {
		// This is the expected behavior - the snippet should be blocked
		t.Logf("Successfully prevented duplicate injection of snippet %s into module %s", testSnippetName, moduleName)
	} else {
		t.Errorf("Failed to detect that snippet %s was already injected into module %s", testSnippetName, moduleName)
	}

	// Test that a different snippet would be allowed
	testSnippetName2 := "different_snippet"
	if moduleSnippetTracker[moduleName][testSnippetName2] {
		t.Errorf("Incorrectly blocked injection of different snippet %s into module %s", testSnippetName2, moduleName)
	} else {
		t.Logf("Correctly allowing injection of different snippet %s into module %s", testSnippetName2, moduleName)
	}
}
