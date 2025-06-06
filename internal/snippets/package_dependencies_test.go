package snippets

import (
	"strings"
	"testing"

	"github.com/toby-bro/pfuzz/internal/verilog"
)

// TestSnippetPackageDependencyResolution tests that package dependencies are properly included in generated snippets
func TestSnippetPackageDependencyResolution(t *testing.T) {
	// Test content with a package and a module that imports it
	testContent := `
package operation_pkg;
    typedef enum logic [2:0] {
        ADD     = 3'b000,
        SUB     = 3'b001,
        MUL     = 3'b010,
        DIV     = 3'b011,
        AND     = 3'b100,
        OR      = 3'b101,
        XOR     = 3'b110,
        INVALID = 3'b111
    } operation_t;
endpackage

module enum_cast (
    input  logic        clk,
    input  logic        reset_n,
    input  logic [2:0]  op_code,
    output logic [7:0]  result
);
    
    import operation_pkg::*;
    
    operation_t current_op;
    logic [7:0] a, b;
    
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            current_op <= ADD;
            a <= 8'd0;
            b <= 8'd0;
        end else begin
            current_op <= operation_t'(op_code);
            a <= 8'd10;
            b <= 8'd5;
        end
    end
    
    always_comb begin
        case (current_op)
            ADD: result = a + b;
            SUB: result = a - b;
            MUL: result = a * b;
            DIV: result = a / b;
            AND: result = a & b;
            OR:  result = a | b;
            XOR: result = a ^ b;
            default: result = 8'd0;
        endcase
    end
endmodule
`

	// Parse the content
	svFile, err := verilog.ParseVerilog(testContent, 0)
	if err != nil {
		t.Fatalf("Failed to parse test content: %v", err)
	}

	// Verify dependency tracking works - enum_cast should depend on operation_pkg
	if deps, exists := svFile.DependencyMap["enum_cast"]; exists {
		found := false
		for _, dep := range deps.DependsOn {
			if dep == "operation_pkg" {
				found = true
				break
			}
		}
		if !found {
			t.Error("Expected enum_cast to depend on operation_pkg")
		}
	} else {
		t.Error("Expected enum_cast to be found in dependency map")
	}

	// Create snippet
	enumCastModule := svFile.Modules["enum_cast"]
	if enumCastModule == nil {
		t.Fatal("enum_cast module not found")
	}

	snippet := &Snippet{
		Name:       enumCastModule.Name,
		Module:     enumCastModule,
		ParentFile: svFile,
	}

	// Create target file for snippet
	targetFile := verilog.NewVerilogFile("enum_cast.sv")

	// Add dependencies
	err = AddDependencies(targetFile, snippet)
	if err != nil {
		t.Fatalf("Failed to add dependencies: %v", err)
	}

	// Verify that operation_pkg is included in the target file
	if _, exists := targetFile.Packages["operation_pkg"]; !exists {
		t.Error("Expected operation_pkg to be included in snippet dependencies")
	}

	// Generate the content and verify it includes the package
	content, err := verilog.PrintVerilogFile(targetFile)
	if err != nil {
		t.Fatalf("Failed to print Verilog file: %v", err)
	}

	if !strings.Contains(content, "package operation_pkg") {
		t.Error("Expected generated content to contain operation_pkg definition")
	}

	if !strings.Contains(content, "module enum_cast") {
		t.Error("Expected generated content to contain enum_cast definition")
	}

	if !strings.Contains(content, "import operation_pkg::*") {
		t.Error("Expected generated content to contain package import statement")
	}
}
