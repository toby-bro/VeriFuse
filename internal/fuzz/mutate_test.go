package fuzz

import (
	"os"
	"strings"
	"testing"

	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

func TestMain(m *testing.M) {
	logger = utils.NewDebugLogger(5)
	exitCode := m.Run()
	os.Exit(exitCode)
}

const (
	sampleVerilogContent = `
// Comment line
module module1 (input clk, output reg out1);
  assign out1 = clk;
endmodule

module module2 #(parameter WIDTH=8) (input logic [WIDTH-1:0] data_in, output logic valid_out);
  // Another comment
  assign valid_out = |data_in;

  /* Multi
     line
     comment */
endmodule

module module3 (); // No ports
endmodule

module simple_sub(
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [8:0] sum
);
    // Simple adder logic
    assign sum = a - b;
endmodule

`
	originalModuleContent = `
module DUT (
    input logic clk,
    input logic rst_n,
    input logic [7:0] data_in,
    output logic [7:0] data_out,
    output logic valid_out
);

    logic [7:0] internal_wire;

    assign internal_wire = data_in + 1;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_out <= 8'b0;
            valid_out <= 1'b0;
        end else begin
            data_out <= internal_wire;
            valid_out <= |internal_wire;
        end
    end

endmodule
`
	snippetToAdd = `
module GGG_for_loop (
    input logic GGGin,
    output logic [3:0] GGGout
);
    integer GGGi;
    always_comb begin
        for (GGGi = 0; GGGi < 4; GGGi = GGGi + 1) begin
            GGGout[GGGi] = GGGin;
        end
        //INJECT
    end
endmodule
`
	snippetWithInjectMarker = `
module GGG_always_comb (
    input logic GGGin,
    output logic GGGout
);
    always_comb begin
        //INJECT
        GGGout = GGGin;
    end
endmodule
`
	originalWithCodeLines = `
module SourceModule ( input a, output b );
    logic x;
    // comment
    assign x = a & 1'b1; // line 1 to inject
    if (a) begin          // line 2 to inject
        x <= 1'b0;
    end
    assign b = x;
endmodule
`
)

func TestAddCodeToSnippet(t *testing.T) {
	modifiedSnippet, err := AddCodeToSnippet(originalWithCodeLines, snippetWithInjectMarker)
	if strings.Contains(err.Error(), "AddCodeToSnippet not implemented yet") {
		t.Skipf("AddCodeToSnippet not implemented yet: %v", err)
	}
	if err != nil {
		t.Fatalf("AddCodeToSnippet failed: %v", err)
	}

	if strings.Contains(modifiedSnippet, "//INJECT") {
		t.Errorf("Modified snippet still contains '//INJECT' marker")
	}

	line1Part := "assign x = a & 1'b1;"
	line2Part := "if (a) begin"
	foundInjectedCode := strings.Contains(modifiedSnippet, line1Part) ||
		strings.Contains(modifiedSnippet, line2Part)

	if !foundInjectedCode {
		t.Errorf("Modified snippet does not seem to contain injected code lines")
	}

	if !strings.Contains(modifiedSnippet, "module GGG_always_comb (") {
		t.Errorf("Modified snippet missing original module definition")
	}
	if !strings.Contains(modifiedSnippet, "GGGout = GGGin;") {
		t.Errorf("Modified snippet missing original assignment 'GGGout = GGGin;'")
	}

	originalNoCode := `
module SourceModule ( input a, output b );
    // only comments
    // and declarations
    input x;
    output y;
endmodule
`
	modifiedSnippetNoCode, err := AddCodeToSnippet(originalNoCode, snippetWithInjectMarker)
	if err != nil {
		t.Fatalf("AddCodeToSnippet failed for no-code case: %v", err)
	}
	if strings.Contains(modifiedSnippetNoCode, "//INJECT") {
		t.Errorf("Modified snippet (no code case) still contains '//INJECT' marker")
	}
	if strings.Contains(modifiedSnippetNoCode, "only comments") ||
		strings.Contains(modifiedSnippetNoCode, "input x") {
		t.Errorf("Modified snippet (no code case) incorrectly injected comments or declarations")
	}
	expectedNoCode := `
module GGG_always_comb (
    input logic GGGin,
    output logic GGGout
);
    always_comb begin
        
        GGGout = GGGin;
    end
endmodule
`
	normalize := func(s string) string {
		return strings.Join(strings.Fields(s), " ")
	}
	if normalize(modifiedSnippetNoCode) != normalize(expectedNoCode) {
		t.Errorf("Modified snippet (no code case) structure differs from expected.")
	}
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
	snippet := &Snippet{
		Name:       "SnippetModule",
		Module:     snippetFile.Modules["SnippetModule"],
		ParentFile: snippetFile,
	}

	variables, err := verilog.ParseVariables(verilogFile, module.Body)
	if err != nil {
		t.Fatalf("ParseVariables failed: %v", err)
	}

	portConnections, newDeclarations, err := matchVariablesToSnippetPorts(
		module,
		snippet,
		variables,
	)
	if err != nil {
		t.Fatalf("matchVariablesToSnippetPorts failed: %v", err)
	}

	if len(portConnections) != 4 {
		t.Errorf("Expected 3 port connections, got %d", len(portConnections))
	}

	if portConnections["input1"] != "data_in1" {
		t.Errorf("Expected 'input1' to connect to 'data_in', got '%s'", portConnections["input1"])
	}

	if portConnections["input2"] != "data_in2" {
		t.Errorf("Expected 'input1' to connect to 'data_in', got '%s'", portConnections["input1"])
	}

	if portConnections["output1"] != "data_out" {
		t.Errorf("Expected 'output1' to have a connection, but it is empty")
	}

	if portConnections["output2"] == "" {
		t.Errorf("Expected 'output2' to have a connection, but it is empty")
	}

	if len(newDeclarations) != 1 {
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
	snippet := &Snippet{
		Name:       "SnippetModule",
		Module:     snippetFile.Modules["SnippetModule"],
		ParentFile: snippetFile,
	}

	err = injectSnippetInModule(module, snippet)
	if err != nil {
		t.Fatalf("injectSnippetInModule failed: %v", err)
	}
	mutatedContent := module.Body

	if !strings.Contains(mutatedContent, "SnippetModule SnippetModule_inst_") {
		t.Errorf("Expected snippet instantiation not found in mutated content")
	}

	if !strings.Contains(mutatedContent, ".output1(data_out)") {
		t.Errorf("Expected output connection not found in mutated content")
	}
	if !strings.Contains(mutatedContent, ".input1(internal_wire)") {
		t.Errorf("Expected input connection not found in mutated content")
	}
}

func TestFindMatchingVariable(t *testing.T) {
	variables := []*verilog.Variable{
		{Name: "data_in", Type: verilog.LOGIC, Width: 8},
		{Name: "data_out", Type: verilog.LOGIC, Width: 8},
		{Name: "control", Type: verilog.BIT, Width: 1},
	}
	port := verilog.Port{Name: "input1", Type: verilog.LOGIC, Width: 8}

	matchedVariable := findMatchingVariable(port, variables, nil)
	if matchedVariable == nil {
		t.Fatalf("findMatchingVariable failed to find a match")
	}

	if matchedVariable.Name != "data_in" {
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

	variables, err := verilog.ParseVariables(verilogFile, module.Body)
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
	expected := "logic signed [7:0] inj_output1;"

	if declaration != expected {
		t.Errorf("Expected '%s', got '%s'", expected, declaration)
	}

	portScalar := verilog.Port{Name: "output2", Type: verilog.LOGIC, Width: 1, IsSigned: false}
	signalNameScalar := "inj_output2"

	declarationScalar := generateSignalDeclaration(portScalar, signalNameScalar)
	expectedScalar := "logic inj_output2;"

	if declarationScalar != expectedScalar {
		t.Errorf("Expected '%s', got '%s'", expectedScalar, declarationScalar)
	}
}

func TestGenerateSnippetInstantiation(t *testing.T) {
	snippet := &Snippet{
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
	if !strings.HasPrefix(instantiation, expectedPrefix) {
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

func TestGetSnippets(t *testing.T) {
	snippets, _, err := getSnippets()
	if err != nil {
		t.Fatalf("getSnippets failed: %v", err)
	}
	if len(snippets) == 0 {
		t.Fatalf("getSnippets returned no snippets")
	}
}
