package verilog

import (
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
)

// Helper function to create a temporary Verilog file
func createTempVerilogFile(t *testing.T, content string, filename string) string {
	t.Helper()
	dir := t.TempDir()
	filePath := filepath.Join(dir, filename)
	err := os.WriteFile(filePath, []byte(content), 0o644)
	if err != nil {
		t.Fatalf("Failed to create temp file %s: %v", filePath, err)
	}
	return filePath
}

func TestParsePortDeclaration(t *testing.T) {
	testCases := []struct {
		name         string
		line         string
		expectedPort *Port
		expectedOK   bool
	}{
		{
			name: "Simple input",
			line: "input logic clk;",
			expectedPort: &Port{
				Name:      "clk",
				Direction: INPUT,
				Type:      LOGIC,
				Width:     0,
				IsSigned:  false,
			},
			expectedOK: true,
		},
		{
			name: "Simple output with range",
			line: "output logic [7:0] data_out;",
			expectedPort: &Port{
				Name:      "data_out",
				Direction: OUTPUT,
				Type:      LOGIC,
				Width:     8,
				IsSigned:  false,
			},
			expectedOK: true,
		},
		{
			name: "Input wire",
			line: "input wire [31:0] data_in;",
			expectedPort: &Port{
				Name:      "data_in",
				Direction: INPUT,
				Type:      WIRE,
				Width:     32,
				IsSigned:  false,
			},
			expectedOK: true,
		},
		{
			name: "Input reg signed",
			line: "input reg signed [15:0] addr;",
			expectedPort: &Port{
				Name:      "addr",
				Direction: INPUT,
				Type:      REG,
				Width:     16,
				IsSigned:  true,
			},
			expectedOK: true,
		},
		{
			name: "Input default type",
			line: "input enable;",
			expectedPort: &Port{
				Name:      "enable",
				Direction: INPUT,
				Type:      LOGIC,
				Width:     0,
				IsSigned:  false,
			},
			expectedOK: true,
		},
		{
			name: "Inout port",
			line: "inout [7:0] io_bus;",
			expectedPort: &Port{
				Name:      "io_bus",
				Direction: INOUT,
				Type:      LOGIC,
				Width:     8,
				IsSigned:  false,
			},
			expectedOK: true,
		},
		{
			name: "Output bit",
			line: "output bit status;",
			expectedPort: &Port{
				Name:      "status",
				Direction: OUTPUT,
				Type:      BIT,
				Width:     0,
				IsSigned:  false,
			},
			expectedOK: true,
		},
		{
			name: "Input active low reset",
			line: "input reset_n;",
			expectedPort: &Port{
				Name:      "reset_n",
				Direction: INPUT,
				Type:      LOGIC,
				Width:     0,
				IsSigned:  false,
			},
			expectedOK: true,
		},
		{
			name: "Port not in header list (should still parse)",
			line: "input logic not_a_port;",
			expectedPort: &Port{
				Name:      "not_a_port",
				Direction: INPUT,
				Type:      LOGIC,
				Width:     0,
				IsSigned:  false,
			},
			expectedOK: true,
		},
		{
			name:         "Not a port declaration",
			line:         "wire internal_signal;",
			expectedPort: nil,
			expectedOK:   false,
		},
		{
			name: "Line with comment",
			line: "input logic clk; // Clock signal",
			expectedPort: &Port{
				Name:      "clk",
				Direction: INPUT,
				Type:      LOGIC,
				Width:     0,
				IsSigned:  false,
			},
			expectedOK: true,
		},
		{
			name: "Extra whitespace",
			line: "  output   logic   [ 7 : 0 ]   data_out  ;  ",
			expectedPort: &Port{
				Name:      "data_out",
				Direction: OUTPUT,
				Type:      LOGIC,
				Width:     8,
				IsSigned:  false,
			},
			expectedOK: true,
		},
		{
			name: "Input integer type",
			line: "input integer count;",
			expectedPort: &Port{
				Name:      "count",
				Direction: INPUT,
				Type:      INTEGER,
				Width:     0,
				IsSigned:  false,
			},
			expectedOK: true,
		},
		{
			name: "Output unsigned",
			line: "output logic unsigned [3:0] flags;",
			expectedPort: &Port{
				Name:      "flags",
				Direction: OUTPUT,
				Type:      LOGIC,
				Width:     4,
				IsSigned:  false,
			},
			expectedOK: true,
		},
	}

	// Create an empty parameters map for testing standard declarations
	emptyParams := make(map[string]Parameter)

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			// Pass emptyParams to the function
			port, ok := parsePortDeclaration(tc.line, emptyParams)

			if ok != tc.expectedOK {
				t.Errorf("parsePortDeclaration(%q) ok = %v; want %v", tc.line, ok, tc.expectedOK)
			}

			if !reflect.DeepEqual(port, tc.expectedPort) {
				t.Errorf(
					"parsePortDeclaration(%q) port = %+v; want %+v",
					tc.line,
					port,
					tc.expectedPort,
				)
			}
		})
	}
}

// Optional: Add tests specifically for parseRange if needed, though it's indirectly tested above.
func TestParseRange(t *testing.T) {
	// Add a test case for parameter resolution
	paramMap := map[string]Parameter{
		"WIDTH": {Name: "WIDTH", DefaultValue: "16"},
		"ADDR":  {Name: "ADDR", DefaultValue: "32"},
	}

	testCases := []struct {
		name          string
		rangeStr      string
		params        map[string]Parameter // Add params to test cases
		expectedWidth int
		expectError   bool
	}{
		{"Empty", "", nil, 0, false},
		{"Simple [7:0]", "[7:0]", nil, 8, false},
		{"Simple [31:0]", "[31:0]", nil, 32, false},
		{"Simple [0:0]", "[0:0]", nil, 1, false},
		{"Whitespace [ 15 : 0 ]", "[ 15 : 0 ]", nil, 16, false},
		{"Special 32-bit", "[32-1:0]", nil, 32, false},
		{"Keyword '32'", "[width_32-1:0]", nil, 32, false},
		{"Keyword 'word'", "[word_size-1:0]", nil, 32, false},
		{"Keyword 'addr'", "[addr_width-1:0]", nil, 32, false},
		{"Keyword 'data'", "[data_width-1:0]", nil, 32, false},
		{"Keyword 'byte'", "[byte_width-1:0]", nil, 8, false},
		{"Default Guess", "[complex_expr]", nil, 8, true}, // Default fallback
		// Parameterized cases
		{"Param [WIDTH-1:0]", "[WIDTH-1:0]", paramMap, 16, false},
		{"Param [ADDR-1:0]", "[ADDR-1:0]", paramMap, 32, false},
		{
			"Param Missing [SIZE-1:0]",
			"[SIZE-1:0]",
			paramMap,
			8,
			true,
		}, // Param not found, fallback
		{
			"Param Non-numeric [NAME-1:0]",
			"[NAME-1:0]",
			map[string]Parameter{"NAME": {DefaultValue: "\"abc\""}},
			8,
			true,
		}, // Non-numeric, fallback
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			// Pass the specific params map for the test case
			width, err := ParseRange(tc.rangeStr, tc.params)
			hasError := (err != nil)

			if hasError != tc.expectError {
				t.Errorf(
					"parseRange(%q) error = %v; want error %v",
					tc.rangeStr,
					err,
					tc.expectError,
				)
			}
			if width != tc.expectedWidth {
				t.Errorf("parseRange(%q) width = %d; want %d", tc.rangeStr, width, tc.expectedWidth)
			}
		})
	}
}

// New test function for ParseVerilogFile
func TestParseVerilogFile(t *testing.T) {
	testCases := []struct {
		name                string
		content             string
		filename            string // Filename to simulate
		targetModule        string // Optional target module name
		expectedModule      *Module
		expectError         bool
		expectedErrorSubstr string
	}{
		{
			name: "Simple Adder SV",
			content: `
module simple_adder (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [8:0] sum
);
    // Simple adder logic
    assign sum = a + b;
endmodule
`,
			filename: "simple_adder.sv",
			expectedModule: &Module{
				Name: "simple_adder",
				Ports: []Port{
					{Name: "a", Direction: INPUT, Type: LOGIC, Width: 8, IsSigned: false},
					{Name: "b", Direction: INPUT, Type: LOGIC, Width: 8, IsSigned: false},
					{Name: "sum", Direction: OUTPUT, Type: LOGIC, Width: 9, IsSigned: false},
				},
				Parameters: []Parameter{},
				// Content will be filled by parser
			},
			expectError: false,
		},
		{
			name: "Parameterized Module SV",
			content: `
module parameterized_module #(
    parameter WIDTH = 8
) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    assign out = in;
endmodule
`,
			filename: "parameterized_module.sv",
			expectedModule: &Module{
				Name: "parameterized_module",
				Ports: []Port{
					// Width should now be correctly resolved to 8
					{Name: "in", Direction: INPUT, Type: LOGIC, Width: 8, IsSigned: false},
					{Name: "out", Direction: OUTPUT, Type: LOGIC, Width: 8, IsSigned: false},
				},
				Parameters: []Parameter{
					{
						Name:         "WIDTH",
						Type:         "", // Type parsing might still be basic
						DefaultValue: "8",
					},
				},
				// Content will be filled by parser
			},
			expectError: false,
		},
		{
			name: "No Module Found",
			content: `
// This file has no module definition
wire x;
assign x = 1'b1;
`,
			filename:            "no_module.sv",
			expectError:         true,
			expectedErrorSubstr: "no module found",
		},
		{
			name:                "Empty File",
			content:             ``,
			filename:            "empty.sv",
			expectError:         true,
			expectedErrorSubstr: "no module found",
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			filePath := createTempVerilogFile(t, tc.content, tc.filename)
			// Ensure expected module has correct filename and content for comparison
			if tc.expectedModule != nil {
				tc.expectedModule.Body = tc.content
			}

			module, err := ParseVerilogFile(filePath, tc.targetModule)

			hasError := (err != nil)
			if hasError != tc.expectError {
				t.Fatalf("ParseVerilogFile() error = %v, expectError %v", err, tc.expectError)
			}
			if tc.expectError && err != nil {
				if tc.expectedErrorSubstr != "" &&
					!strings.Contains(err.Error(), tc.expectedErrorSubstr) {
					t.Errorf(
						"ParseVerilogFile() error = %q, expected substring %q",
						err,
						tc.expectedErrorSubstr,
					)
				}
				// Don't compare module struct if error was expected
				return
			}

			// Compare modules (excluding Content for simplicity if needed, but include for now)
			if !reflect.DeepEqual(module, tc.expectedModule) {
				// Use %+v for better struct diff visibility
				t.Errorf(
					"ParseVerilogFile() returned module:\n%+v\nExpected module:\n%+v",
					module,
					tc.expectedModule,
				)
				// Optionally print specific diffs
				if module == nil || tc.expectedModule == nil {
					t.Errorf("One of the modules is nil, cannot compare details.")
					return // Avoid panic on nil pointers
				}
				if len(module.Ports) != len(tc.expectedModule.Ports) {
					t.Errorf(
						"Port count mismatch: got %d, want %d",
						len(module.Ports),
						len(tc.expectedModule.Ports),
					)
				} else {
					for i := range module.Ports {
						if !reflect.DeepEqual(module.Ports[i], tc.expectedModule.Ports[i]) {
							t.Errorf("Port %d mismatch: got %+v, want %+v", i, module.Ports[i], tc.expectedModule.Ports[i])
						}
					}
				}
				if len(module.Parameters) != len(tc.expectedModule.Parameters) {
					t.Errorf(
						"Parameter count mismatch: got %d, want %d",
						len(module.Parameters),
						len(tc.expectedModule.Parameters),
					)
				} else {
					for i := range module.Parameters {
						if !reflect.DeepEqual(module.Parameters[i], tc.expectedModule.Parameters[i]) {
							t.Errorf("Parameter %d mismatch: got %+v, want %+v", i, module.Parameters[i], tc.expectedModule.Parameters[i])
						}
					}
				}
			}
		})
	}
}

var aa = `rand logic [7:0] GGG_field1;
    rand int unsigned GGG_field2;
bit GGG_condition_var;
rand logic [7:0] GGG_array_var [GGG_CONTAINER_SIZE];
    int GGG_index_limit; // Member to use in constraint expression
int 	m_queue [$]; 
    rand logic [GGG_CLASS_WIDTH-1:0] GGG_class_rand_var;
		myPacket pkt0, pkt1;
logic [7:0] internal_wire;

	`

func TestParseVariables(t *testing.T) {
	expectedVars := []*Variable{
		{Name: "GGG_field1", Type: LOGIC, Width: 8, Unsigned: false},
		{Name: "GGG_field2", Type: INT, Width: 32, Unsigned: true},
		{Name: "GGG_condition_var", Type: BIT, Width: 1, Unsigned: false},
		{
			Name:     "GGG_array_var",
			Type:     LOGIC,
			Width:    8,
			Unsigned: false,
		}, // Array attribute not checked here
		{Name: "GGG_index_limit", Type: INT, Width: 32, Unsigned: false},
		{
			Name:     "m_queue",
			Type:     INT,
			Width:    32,
			Unsigned: false,
		}, // Array attribute not checked here
		// For GGG_class_rand_var, ParseRange with nil parameters will default to width 8 for "[GGG_CLASS_WIDTH-1:0]"
		{Name: "GGG_class_rand_var", Type: LOGIC, Width: 8, Unsigned: false},
		{Name: "internal_wire", Type: LOGIC, Width: 8, Unsigned: false},
	}

	// Pass nil for VerilogFile as 'aa' contains only basic types for this test's scope,
	// and we are not testing user-defined type resolution here.
	// The `myPacket pkt0, pkt1;` line in `aa` will be skipped by MatchAllVariablesFromString
	// because `myPacket` is not a built-in type in the generalVariableRegex.
	parsedVars, err := ParseVariables(nil, aa)
	if err != nil {
		t.Fatalf("ParseVariables failed: %v", err)
	}

	if len(parsedVars) != len(expectedVars) {
		t.Fatalf("Expected %d variables, got %d variables.", len(expectedVars), len(parsedVars))
	}

	for i, expected := range expectedVars {
		actual := parsedVars[i]
		// Compare relevant fields. ParentStruct, ParentClass, Array are not set by this parsing path or are nil/empty.
		if actual.Name != expected.Name ||
			actual.Type != expected.Type ||
			actual.Width != expected.Width ||
			actual.Unsigned != expected.Unsigned {
			t.Errorf(
				"Variable %d ('%s') mismatch:\nExpected: Name=%s, Type=%d, Width=%d, Unsigned=%t\nActual:   Name=%s, Type=%d, Width=%d, Unsigned=%t",
				i,
				expected.Name,
				expected.Name,
				expected.Type,
				expected.Width,
				expected.Unsigned,
				actual.Name,
				actual.Type,
				actual.Width,
				actual.Unsigned,
			)
		}
	}
}

var bb = `typedef struct packed {
    rand logic [7:0] GGG_field1;
    rand int unsigned GGG_field2;
    // INJECT - Struct body
} GGG_my_struct_t;`

func TestStructRegex(t *testing.T) {
	// Test the regex for struct
	matches := MatchAllStructsFromString(bb)
	if len(matches) == 0 {
		t.Errorf("No matches found for struct regex")
	} else {
		t.Logf("Found %d structs", len(matches))
	}
}

var cc = `// Class to contain rand variables and constraint with 'if'
class GGG_ConstraintIfContainer;
    rand int GGG_rand_var1;
    rand int GGG_rand_var2;
    bit GGG_condition_var; // Member to control constraint branch

    // Constraint with if
    constraint GGG_if_constr {
        if (GGG_condition_var) {
            GGG_rand_var1 < GGG_rand_var2;
            //INJECT - Constraint if body
        } else {
            GGG_rand_var1 == GGG_rand_var2;
        }
        GGG_rand_var1 inside {[-100:100]};
        GGG_rand_var2 inside {[-100:100]};
         //INJECT - Constraint if end body
    }
    // INJECT - Constraint if container class body
endclass`

func TestClassRegex(t *testing.T) {
	// Test the regex for class
	matches := MatchAllClassesFromString(cc)
	if len(matches) == 0 {
		t.Errorf("No matches found for class regex")
	} else {
		t.Logf("Found %d classes", len(matches))
	}
}

var dd = `
typedef struct packed {
    rand logic [7:0] GGG_field1;
    rand int unsigned GGG_field2;
    // INJECT - Struct body
} GGG_my_struct_t;

class GGG_StructRandContainer;
    rand GGG_my_struct_t GGG_struct_var;
    // INJECT - Struct rand container class body
endclass

module GGG_StructuredRandModule (
    input logic [7:0] GGGin,
    output logic [15:0] GGGout
);
    // Instantiate the class containing the structured rand variable
    GGG_StructRandContainer GGG_struct_h = new();

    always_comb begin
        //INJECT
        if (GGG_struct_h != null) begin
            GGGout = {GGG_struct_h.GGG_struct_var.GGG_field1, GGG_struct_h.GGG_struct_var.GGG_field2[7:0]};
        end else begin
            GGGout = 0;
        end
        //INJECT
    end
    // INJECT - Structured rand module body
endmodule
`

func TestCompleteParsing(t *testing.T) {
	vfile, err := ParseVerilog(dd)
	if err != nil {
		t.Fatalf("Failed to parse Verilog: %v", err)
	}
	if vfile == nil {
		t.Fatalf("Parsed Verilog file is nil")
	}
	if len(vfile.Modules) == 0 {
		t.Fatalf("No modules found in parsed Verilog file")
	}
	if len(vfile.Classes) == 0 {
		t.Fatalf("No classes found in parsed Verilog file")
	}
	if len(vfile.Structs) == 0 {
		t.Fatalf("No structs found in parsed Verilog file")
	}
	if len(vfile.DependancyMap) == 0 {
		t.Fatalf("No dependencies found in parsed Verilog file")
	}
	if value, isMapContainsKey := vfile.DependancyMap["GGG_StructRandContainer"]; !isMapContainsKey {
		t.Fatalf("Dependency map does not contain key GGG_StructRandContainer")
	} else if value.DependsOn[0] != "GGG_my_struct_t" {
		t.Fatalf("Dependency map value does not contain expected value GGG_my_struct_t")
	}

	if value, isMapContainsKey := vfile.DependancyMap["GGG_StructuredRandModule"]; !isMapContainsKey {
		t.Fatalf("Dependency map does not contain key GGG_StructuredRandModule")
	} else if value.DependsOn[0] != "GGG_StructRandContainer" {
		t.Fatalf("Dependency map value does not contain expected value GGG_StructRandContainer")
	}

	t.Logf("Successfully parsed Verilog file with %d modules, %d classes, and %d structs",
		len(vfile.Modules),
		len(vfile.Classes),
		len(vfile.Structs),
	)
}

var ee = `
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

func TestParseModules(t *testing.T) {
	// Test the regex for module
	vf := VerilogFile{
		Classes: make(map[string]*Class),
		Structs: make(map[string]*Struct),
	}
	err := vf.ParseModules(ee)
	if err != nil {
		t.Fatalf("Failed to parse modules: %v", err)
	}
	modules := vf.Modules
	if len(modules) != 3 {
		t.Errorf("Ouin ouin not enough modules found, got %d, want 3", len(modules))
	}
}
