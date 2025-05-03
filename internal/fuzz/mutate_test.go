package fuzz

import (
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

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

func TestExtractModules(t *testing.T) {
	tempDir := t.TempDir()
	tempFile := filepath.Join(tempDir, "test.sv")
	err := os.WriteFile(tempFile, []byte(sampleVerilogContent), 0o644)
	if err != nil {
		t.Fatalf("Failed to write temp file: %v", err)
	}

	modules, err := ExtractModules(tempFile)
	if err != nil {
		t.Fatalf("ExtractModules failed: %v", err)
	}

	expectedCount := 4
	if len(modules) != expectedCount {
		t.Errorf("Expected %d modules, got %d", expectedCount, len(modules))
	}

	expectedKey1 := "test.sv_module1"
	expectedKey2 := "test.sv_module2"
	expectedKey3 := "test.sv_module3"
	expectedKey4 := "test.sv_simple_sub"

	if _, ok := modules[expectedKey1]; !ok {
		t.Errorf("Expected module key '%s' not found", expectedKey1)
	}
	if _, ok := modules[expectedKey2]; !ok {
		t.Errorf("Expected module key '%s' not found", expectedKey2)
	}
	if _, ok := modules[expectedKey3]; !ok {
		t.Errorf("Expected module key '%s' not found", expectedKey3)
	}
	if _, ok := modules[expectedKey4]; !ok {
		t.Errorf("Expected module key '%s' not found", expectedKey4)
	}

	if !strings.Contains(modules[expectedKey1], "module module1 (input clk, output reg out1);") {
		t.Errorf("Content for module1 seems incorrect")
	}
	if !strings.Contains(modules[expectedKey1], "endmodule") {
		t.Errorf("Content for module1 missing endmodule")
	}
}

func TestInjectSnippet(t *testing.T) {
	mutatedContent, err := InjectSnippet(originalModuleContent, snippetToAdd)
	if err != nil {
		t.Fatalf("InjectSnippet failed: %v", err)
	}

	// Check 1: Snippet definition is present
	if !strings.Contains(mutatedContent, "module GGG") {
		t.Errorf("Mutated content missing snippet definition 'module GGG'")
	}

	instantiationRegex := regexp.MustCompile(`GGG\w+\s+GGG\w+\d+\s+\(`)
	if !instantiationRegex.MatchString(mutatedContent) {
		t.Errorf("Mutated content missing snippet instantiation matching 'GGG... ('")
	}

	declarationRegex := regexp.MustCompile(`logic\s+inj_output_gggout_\d+;`)
	if !declarationRegex.MatchString(mutatedContent) {
		t.Errorf("Missing expected declaration matching 'logic inj_output_gggout_...;'")
	}

	endModuleIndex := strings.LastIndex(mutatedContent, "endmodule")
	instantiationMatch := instantiationRegex.FindStringIndex(mutatedContent)
	declarationMatch := declarationRegex.FindStringIndex(mutatedContent)

	if endModuleIndex == -1 {
		t.Fatalf("Could not find 'endmodule' in output")
	}
	if instantiationMatch == nil {
		t.Fatalf("Could not find instantiation in output")
	}
	if declarationMatch == nil {
		t.Fatalf("Could not find declaration in output")
	}

	if !(declarationMatch[0] < endModuleIndex && instantiationMatch[0] < endModuleIndex) {
		t.Errorf("Instantiation or declaration is not placed correctly before the final endmodule")
	}

	if !strings.Contains(mutatedContent, "module DUT (") {
		t.Errorf("Original module definition 'module DUT (' missing")
	}
	if !strings.Contains(mutatedContent, "always_ff @(posedge clk or negedge rst_n)") {
		t.Errorf("Original always_ff block missing")
	}

	connectionRegex := regexp.MustCompile(`\.GGGin\s*\(\s*GGGin\s*\)`)
	if !connectionRegex.MatchString(mutatedContent) {
		t.Errorf("Expected input connection '.GGGin(GGGin)' not found or incorrect")
	}
}

func TestAddCodeToSnippet(t *testing.T) {
	modifiedSnippet, err := AddCodeToSnippet(originalWithCodeLines, snippetWithInjectMarker)
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

func TestGetSnippetsAndRandom(t *testing.T) {
	originalSnippets := snippets
	testSnippets := []string{"module snip1(); endmodule", "module snip2(input a); endmodule"}
	snippets = testSnippets
	defer func() { snippets = originalSnippets }()

	retrievedSnippets, err := GetSnippets()
	if err != nil {
		t.Fatalf("GetSnippets failed: %v", err)
	}
	if len(retrievedSnippets) != len(testSnippets) {
		t.Errorf(
			"GetSnippets returned %d snippets, expected %d",
			len(retrievedSnippets),
			len(testSnippets),
		)
	}
	if retrievedSnippets[0] != testSnippets[0] || retrievedSnippets[1] != testSnippets[1] {
		t.Errorf("GetSnippets returned incorrect data")
	}

	randomSnippet, err := GetRandomSnippet()
	if err != nil {
		t.Fatalf("GetRandomSnippet failed: %v", err)
	}
	found := false
	for _, s := range testSnippets {
		if randomSnippet == s {
			found = true
			break
		}
	}
	if !found {
		t.Errorf("GetRandomSnippet returned a snippet not in the test set: %s", randomSnippet)
	}
}

// Note: Testing MutateFile directly is complex due to file I/O and randomness.
// Mocking frameworks or more elaborate setup would be needed.
// It's generally better to focus unit tests on the deterministic logic within
// InjectSnippet and AddCodeToSnippet, which are tested above.
