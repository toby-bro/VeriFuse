package verilog_ext

import (
	"os"
	"path/filepath"
	"testing"
)

func TestSystemVerilogAssertionPatterns(t *testing.T) {
	testContent := `
module test_assertions(
    input logic clk,
    input logic rst_n,
    input logic [7:0] data_in,
    output logic prop_out
);
    // Property definitions
    property p_data_valid;
        @(posedge clk) disable iff (!rst_n)
        data_in != 8'h00;
    endproperty
    
    // Assertion statements
    assert property (p_data_valid) else $error("Data validation failed");
    assume property (@(posedge clk) rst_n |-> ##[1:3] data_in > 0);
    cover property (@(posedge clk) data_in == 8'hFF);
    restrict property (@(posedge clk) data_in < 8'hFE);
    
    // Procedural assertions
    always @(posedge clk) begin
        assert (data_in != 8'hZZ) else $fatal("Invalid data");
        assume (rst_n == 1'b0 || rst_n == 1'b1);
        cover (data_in[7:4] == 4'hF);
    end
endmodule`

	// Test assertion property patterns
	assertProps := matchAssertPropertiesFromString(testContent)
	if len(assertProps) == 0 {
		t.Error("Expected to find assert property statements")
	}

	assumeProps := matchAssumePropertiesFromString(testContent)
	if len(assumeProps) == 0 {
		t.Error("Expected to find assume property statements")
	}

	coverProps := matchCoverPropertiesFromString(testContent)
	if len(coverProps) == 0 {
		t.Error("Expected to find cover property statements")
	}

	restrictProps := matchRestrictPropertiesFromString(testContent)
	if len(restrictProps) == 0 {
		t.Error("Expected to find restrict property statements")
	}

	// Test procedural assertion patterns
	assertStmts := matchAssertStatementsFromString(testContent)
	if len(assertStmts) == 0 {
		t.Error("Expected to find assert statements")
	}

	assumeStmts := matchAssumeStatementsFromString(testContent)
	if len(assumeStmts) == 0 {
		t.Error("Expected to find assume statements")
	}

	coverStmts := matchCoverStatementsFromString(testContent)
	if len(coverStmts) == 0 {
		t.Error("Expected to find cover statements")
	}

	// Test property definitions
	properties := matchPropertiesFromString(testContent)
	if len(properties) == 0 {
		t.Error("Expected to find property definitions")
	}

	t.Logf(
		"Found %d assert properties, %d assume properties, %d cover properties, %d restrict properties",
		len(assertProps),
		len(assumeProps),
		len(coverProps),
		len(restrictProps),
	)
	t.Logf("Found %d assert statements, %d assume statements, %d cover statements",
		len(assertStmts), len(assumeStmts), len(coverStmts))
	t.Logf("Found %d property definitions", len(properties))
}

func TestSystemVerilogAlwaysBlockPatterns(t *testing.T) {
	testContent := `
module test_always_blocks(
    input logic clk,
    input logic rst_n,
    input logic enable,
    input logic [7:0] data_in,
    output logic [7:0] data_out,
    output logic valid_out
);
    // Different types of always blocks
    always_comb begin
        valid_out = enable && (data_in != 8'h00);
    end
    
    always_ff @(posedge clk or negedge rst_n) begin : ff_block
        if (!rst_n) begin
            data_out <= 8'h00;
        end else if (enable) begin
            data_out <= data_in;
        end
    end
    
    always_latch @(enable or data_in) begin : latch_block
        if (enable) begin
            data_out = data_in;
        end
    end
    
    always @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            valid_out <= 1'b0;
        end else begin
            valid_out <= enable;
        end
    end
endmodule`

	// Test always block patterns
	alwaysBlocks := matchAlwaysBlocksFromString(testContent)
	if len(alwaysBlocks) < 3 {
		t.Errorf("Expected to find at least 3 always blocks, found %d", len(alwaysBlocks))
	}

	alwaysComb := matchAlwaysCombFromString(testContent)
	if len(alwaysComb) == 0 {
		t.Error("Expected to find always_comb blocks")
	}

	alwaysFF := matchAlwaysFFFromString(testContent)
	if len(alwaysFF) == 0 {
		t.Error("Expected to find always_ff blocks")
	}

	alwaysLatch := matchAlwaysLatchFromString(testContent)
	if len(alwaysLatch) == 0 {
		t.Error("Expected to find always_latch blocks")
	}

	t.Logf("Found %d always blocks total", len(alwaysBlocks))
	t.Logf("Found %d always_comb, %d always_ff, %d always_latch",
		len(alwaysComb), len(alwaysFF), len(alwaysLatch))
}

func TestSystemVerilogInterfaceModportPatterns(t *testing.T) {
	testContent := `
interface test_if;
    logic [31:0] addr;
    logic [31:0] data;
    logic we, re;
    
    modport master (
        output addr,
        output we,
        output re,
        inout data
    );
    
    modport slave (
        input addr,
        input we,
        input re,
        inout data
    );
    
    modport monitor (
        input addr,
        input data,
        input we,
        input re
    );
endinterface

module test_module(
    test_if.master bus_master,
    test_if.slave bus_slave
);
    // Module implementation
endmodule`

	// Test modport patterns
	modports := matchModportsFromString(testContent)
	if len(modports) < 3 {
		t.Errorf("Expected to find at least 3 modports, found %d", len(modports))
	}

	// Check modport names
	expectedModports := []string{"master", "slave", "monitor"}
	foundModports := make([]string, 0)
	for _, match := range modports {
		if len(match) > 1 {
			foundModports = append(foundModports, match[1])
		}
	}

	for _, expected := range expectedModports {
		found := false
		for _, actual := range foundModports {
			if actual == expected {
				found = true
				break
			}
		}
		if !found {
			t.Errorf("Expected to find modport '%s'", expected)
		}
	}

	t.Logf("Found modports: %v", foundModports)
}

func TestSystemVerilogGeneratePatterns(t *testing.T) {
	testContent := `
module test_generate(
    input logic [3:0] sel,
    input logic [7:0] data_in [0:3],
    output logic [7:0] data_out
);
    generate
        if (USE_MUX) begin : mux_gen
            always_comb begin
                case (sel)
                    4'h0: data_out = data_in[0];
                    4'h1: data_out = data_in[1];
                    4'h2: data_out = data_in[2];
                    4'h3: data_out = data_in[3];
                    default: data_out = 8'h00;
                endcase
            end
        end else begin : direct_gen
            assign data_out = data_in[0];
        end
        
        for (genvar i = 0; i < 4; i++) begin : loop_gen
            logic [7:0] temp_reg;
            always_ff @(posedge clk) begin
                temp_reg <= data_in[i];
            end
        end
        
        case (DATA_WIDTH)
            8: begin : width8_gen
                assign data_out = data_in[sel][7:0];
            end
            16: begin : width16_gen
                assign data_out = data_in[sel][15:8];
            end
            default: begin : default_gen
                assign data_out = 8'h00;
            end
        endcase
    endgenerate
endmodule`

	// Test generate patterns
	generateBlocks := matchGenerateBlocksFromString(testContent)
	if len(generateBlocks) == 0 {
		t.Error("Expected to find generate blocks")
	}

	generateIfs := matchGenerateIfsFromString(testContent)
	if len(generateIfs) == 0 {
		t.Error("Expected to find generate if statements")
	}

	generateFors := matchGenerateForsFromString(testContent)
	if len(generateFors) == 0 {
		t.Error("Expected to find generate for loops")
	}

	generateCases := matchGenerateCasesFromString(testContent)
	if len(generateCases) == 0 {
		t.Error("Expected to find generate case statements")
	}

	t.Logf("Found %d generate blocks, %d generate ifs, %d generate fors, %d generate cases",
		len(generateBlocks), len(generateIfs), len(generateFors), len(generateCases))
}

func TestSystemVerilogPragmaPatterns(t *testing.T) {
	testContent := `
module test_pragmas(
    input logic [1:0] sel,
    input logic [3:0] data,
    output logic [3:0] result
);
    always_comb begin
        (* full_case, parallel_case *)
        case (sel)
            2'b00: result = data;
            2'b01: result = ~data;
            2'b10: result = data << 1;
            2'b11: result = data >> 1;
        endcase
        
        (* unique *)
        if (data[3]) begin
            result = 4'hF;
        end else if (data[2]) begin
            result = 4'hE;
        end else begin
            result = 4'h0;
        end
    end
    
    // Synthesis directives
    // synthesis translate_off
    initial begin
        $display("Simulation only code");
    end
    // synthesis translate_on
    
    (* keep = "true" *)
    logic internal_signal;
    
    (* ram_style = "block" *)
    logic [7:0] memory [0:255];
endmodule`

	// Test pragma patterns
	pragmas := matchPragmasFromString(testContent)
	if len(pragmas) == 0 {
		t.Error("Expected to find pragma attributes")
	}

	pragmaAttribs := matchPragmaAttributesFromString(testContent)
	if len(pragmaAttribs) == 0 {
		t.Error("Expected to find pragma attribute assignments")
	}

	synthesisDir := matchSynthesisDirectivesFromString(testContent)
	if len(synthesisDir) == 0 {
		t.Error("Expected to find synthesis directives")
	}

	translateOff := matchTranslateOffFromString(testContent)
	if len(translateOff) == 0 {
		t.Error("Expected to find translate_off directives")
	}

	translateOn := matchTranslateOnFromString(testContent)
	if len(translateOn) == 0 {
		t.Error("Expected to find translate_on directives")
	}

	t.Logf("Found %d pragmas, %d pragma attributes, %d synthesis directives",
		len(pragmas), len(pragmaAttribs), len(synthesisDir))
	t.Logf("Found %d translate_off, %d translate_on", len(translateOff), len(translateOn))
}

func TestSystemVerilogDPIPatterns(t *testing.T) {
	testContent := `
package test_dpi_pkg;
    // DPI function imports
    import "DPI-C" function int c_add(input int a, input int b);
    import "DPI-C" context function string c_get_string(input int index);
    import "DPI-C" pure function real c_sqrt(input real x);
    
    // DPI task imports
    import "DPI-C" task c_print_message(input string msg);
    import "DPI-C" context task c_wait_cycles(input int cycles);
    
    // DPI exports
    export "DPI-C" function sv_callback;
    export "DPI-C" task sv_task_callback;
    
    function int sv_callback(int value);
        return value * 2;
    endfunction
    
    task sv_task_callback(int delay);
        #delay;
    endtask
endpackage`

	// Test DPI patterns
	dpiImports := matchDPIImportsFromString(testContent)
	if len(dpiImports) == 0 {
		t.Error("Expected to find DPI function imports")
	}

	dpiTaskImports := matchDPITaskImportsFromString(testContent)
	if len(dpiTaskImports) == 0 {
		t.Error("Expected to find DPI task imports")
	}

	dpiExports := matchDPIExportsFromString(testContent)
	if len(dpiExports) == 0 {
		t.Error("Expected to find DPI function exports")
	}

	dpiTaskExports := matchDPITaskExportsFromString(testContent)
	if len(dpiTaskExports) == 0 {
		t.Error("Expected to find DPI task exports")
	}

	t.Logf(
		"Found %d DPI function imports, %d DPI task imports",
		len(dpiImports),
		len(dpiTaskImports),
	)
	t.Logf(
		"Found %d DPI function exports, %d DPI task exports",
		len(dpiExports),
		len(dpiTaskExports),
	)
}

func TestSystemVerilogConstraintPatterns(t *testing.T) {
	testContent := `
class test_constraint_class;
    rand bit [7:0] data;
    rand bit [3:0] addr;
    rand bit enable;
    
    constraint valid_data {
        data inside {[1:254]};
        data != 8'hZZ;
        data != 8'hXX;
    }
    
    constraint addr_range {
        addr < 4'hF;
        addr != 4'h0;
    }
    
    constraint enable_dependency {
        enable -> (data > 8'h10);
        !enable -> (data == 8'h00);
    }
    
    function new();
        // Constructor
    endfunction
endclass`

	// Test constraint patterns
	constraints := matchConstraintsFromString(testContent)
	if len(constraints) == 0 {
		t.Error("Expected to find constraint blocks")
	}

	constraintBlocks := matchConstraintBlocksFromString(testContent)
	if len(constraintBlocks) == 0 {
		t.Error("Expected to find constraint block definitions")
	}

	expectedConstraints := []string{"valid_data", "addr_range", "enable_dependency"}
	foundConstraints := make([]string, 0)
	for _, match := range constraints {
		if len(match) > 1 {
			foundConstraints = append(foundConstraints, match[1])
		}
	}

	for _, expected := range expectedConstraints {
		found := false
		for _, actual := range foundConstraints {
			if actual == expected {
				found = true
				break
			}
		}
		if !found {
			t.Errorf("Expected to find constraint '%s'", expected)
		}
	}

	t.Logf("Found constraints: %v", foundConstraints)
}

// Integration test using real SystemVerilog files from the codebase
func TestSystemVerilogPatternsWithRealFiles(t *testing.T) {
	// Test with assert_module.sv which contains assertion patterns
	assertModulePath := "/home/jns/Documents/Berkeley/pfuzz/testfiles/sv/unsupported/assert_module.sv"
	if _, err := os.Stat(assertModulePath); err == nil {
		content, err := os.ReadFile(assertModulePath)
		if err != nil {
			t.Errorf("Failed to read assert_module.sv: %v", err)
			return
		}

		contentStr := string(content)

		// Test assertion patterns
		assertProps := matchAssertPropertiesFromString(contentStr)
		properties := matchPropertiesFromString(contentStr)

		t.Logf(
			"Real file test - assert_module.sv: Found %d assert properties, %d property definitions",
			len(assertProps),
			len(properties),
		)

		if len(assertProps) == 0 && len(properties) == 0 {
			t.Log(
				"Note: No assertion patterns found in assert_module.sv - file may use different syntax",
			)
		}
	}

	// Test with V3Assert files which contain various SystemVerilog constructs
	v3AssertFiles := []string{
		"/home/jns/Documents/Berkeley/pfuzz/isolated/V3Assert/assert_property_mod.sv",
		"/home/jns/Documents/Berkeley/pfuzz/isolated/V3Assert/cover_property_mod.sv",
		"/home/jns/Documents/Berkeley/pfuzz/isolated/V3Assert/assume_property_mod.sv",
		"/home/jns/Documents/Berkeley/pfuzz/isolated/V3Assert/case_pragmas_mod.sv",
	}

	totalAssertProps := 0
	totalCoverProps := 0
	totalAssumeProps := 0
	totalPragmas := 0

	for _, filePath := range v3AssertFiles {
		if _, err := os.Stat(filePath); err == nil {
			content, err := os.ReadFile(filePath)
			if err != nil {
				t.Logf("Failed to read %s: %v", filePath, err)
				continue
			}

			contentStr := string(content)

			assertProps := matchAssertPropertiesFromString(contentStr)
			coverProps := matchCoverPropertiesFromString(contentStr)
			assumeProps := matchAssumePropertiesFromString(contentStr)
			pragmas := matchPragmasFromString(contentStr)

			totalAssertProps += len(assertProps)
			totalCoverProps += len(coverProps)
			totalAssumeProps += len(assumeProps)
			totalPragmas += len(pragmas)

			t.Logf(
				"Real file test - %s: Found %d assert, %d cover, %d assume properties, %d pragmas",
				filepath.Base(
					filePath,
				),
				len(assertProps),
				len(coverProps),
				len(assumeProps),
				len(pragmas),
			)
		}
	}

	t.Logf("Total across V3Assert files: %d assert, %d cover, %d assume properties, %d pragmas",
		totalAssertProps, totalCoverProps, totalAssumeProps, totalPragmas)
}

// ===============================================
// End of Tests for Advanced SystemVerilog Construct Patterns
// ===============================================
