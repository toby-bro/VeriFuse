package main

import (
	"fmt"
	"log"

	"github.com/toby-bro/pfuzz/internal/verilog"
)

func main() {
	// Test content with package and module that imports it
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

	fmt.Println("Testing package dependency detection...")

	// Parse the Verilog content
	svFile, err := verilog.ParseVerilog(testContent, 0)
	if err != nil {
		log.Fatalf("Failed to parse Verilog content: %v", err)
	}

	// Print discovered packages
	fmt.Printf("Found %d packages:\n", len(svFile.Packages))
	for name, pkg := range svFile.Packages {
		fmt.Printf("  - %s\n", name)
		fmt.Printf("    Typedefs: %d\n", len(pkg.Typedefs))
		fmt.Printf("    Imports: %d\n", len(pkg.Imports))
		fmt.Printf("    Variables: %d\n", len(pkg.Variables))
		fmt.Printf("    Parameters: %d\n", len(pkg.Parameters))
	}

	// Print discovered modules
	fmt.Printf("\nFound %d modules:\n", len(svFile.Modules))
	for name, module := range svFile.Modules {
		fmt.Printf("  - %s\n", name)
		fmt.Printf("    Ports: %d\n", len(module.Ports))
	}

	// Print dependency map
	fmt.Printf("\nDependency map:\n")
	for name, deps := range svFile.DependencyMap {
		fmt.Printf("  %s depends on: %v\n", name, deps.DependsOn)
	}

	// Verify that enum_cast depends on operation_pkg
	if deps, exists := svFile.DependencyMap["enum_cast"]; exists {
		found := false
		for _, dep := range deps.DependsOn {
			if dep == "operation_pkg" {
				found = true
				break
			}
		}
		if found {
			fmt.Println("\n✅ SUCCESS: enum_cast correctly depends on operation_pkg")
		} else {
			fmt.Printf("\n❌ FAILURE: enum_cast does not depend on operation_pkg, dependencies: %v\n", deps.DependsOn)
		}
	} else {
		fmt.Println("\n❌ FAILURE: enum_cast not found in dependency map")
	}
}
