package verilog

import (
	"reflect"
	"sort"
	"testing"
)

func TestParseParameters(t *testing.T) {
	testCases := []struct {
		name           string
		paramListStr   string
		expectedParams []*Parameter
	}{
		{
			name:           "Empty parameter list",
			paramListStr:   "",
			expectedParams: []*Parameter{},
		},
		{
			name:         "Extra whitespace",
			paramListStr: "  parameter   int    P_VAL   =  5  ,  NEXT_P  ",
			expectedParams: []*Parameter{
				{Name: "P_VAL", Type: INT, DefaultValue: "5", AnsiStyle: true},
				{Name: "NEXT_P", Type: INT, DefaultValue: "", AnsiStyle: true},
			},
		},
		{
			name:         "Localparam (parsed as parameter)",
			paramListStr: "localparam STATE_IDLE = 0",
			expectedParams: []*Parameter{
				{
					Name:         "STATE_IDLE",
					Type:         LOGIC,
					DefaultValue: "0",
					Localparam:   true,
					AnsiStyle:    true,
				},
			},
		},
		{
			name:           "Malformed - just equals",
			paramListStr:   "= 5",
			expectedParams: []*Parameter{},
		},
		{
			name:           "Malformed - missing name after type",
			paramListStr:   "parameter int = 5",
			expectedParams: []*Parameter{},
		},
		{
			name:           "Malformed - parameter keyword alone",
			paramListStr:   "parameter",
			expectedParams: []*Parameter{},
		},
		{
			name:           "Malformed - parameter with only type",
			paramListStr:   "parameter real",
			expectedParams: []*Parameter{},
		},
		{
			name:         "Multiple parameters",
			paramListStr: "parameter A = 1, B = 2, C = 3",
			expectedParams: []*Parameter{
				{Name: "A", Type: LOGIC, DefaultValue: "1", AnsiStyle: true},
				{Name: "B", Type: INTEGER, DefaultValue: "2", AnsiStyle: true},
				{Name: "C", Type: INTEGER, DefaultValue: "3", AnsiStyle: true},
			},
		},
		{
			name:         "Multiple parameters with types",
			paramListStr: "parameter integer COUNT = 10, parameter real DELAY = 1.2, bit ENABLE = 1'b1",
			expectedParams: []*Parameter{
				{Name: "COUNT", Type: INTEGER, DefaultValue: "10", AnsiStyle: true},
				{Name: "DELAY", Type: REAL, DefaultValue: "1.2", AnsiStyle: true},
				{Name: "ENABLE", Type: BIT, DefaultValue: "1'b1", AnsiStyle: true},
			},
		},
		{
			name:         "Parameter with complex value including function call",
			paramListStr: `P_COMPLEX = $clog2(ANOTHER_PARAM + 1) - 1`,
			expectedParams: []*Parameter{
				{
					Name:         "P_COMPLEX",
					Type:         UNKNOWN,
					DefaultValue: "$clog2(ANOTHER_PARAM + 1) - 1",
					AnsiStyle:    true,
				},
			},
		},
		{
			name:         "Parameter with expression as default value",
			paramListStr: "ADDR_WIDTH = DATA_WIDTH / 2",
			expectedParams: []*Parameter{
				{
					Name:         "ADDR_WIDTH",
					Type:         UNKNOWN,
					DefaultValue: "DATA_WIDTH / 2",
					AnsiStyle:    true,
				},
			},
		},
		{
			name:         "Parameter with string default value",
			paramListStr: `FILENAME = "test.txt"`,
			expectedParams: []*Parameter{
				{Name: "FILENAME", Type: STRING, DefaultValue: `"test.txt"`, AnsiStyle: true},
			},
		},
		{
			name:         "Parameter with trailing comma",
			paramListStr: "P1 = 1,",
			expectedParams: []*Parameter{
				{Name: "P1", Type: LOGIC, DefaultValue: "1", AnsiStyle: true},
			},
		},
		{
			name:         "Parameter with type 'time'",
			paramListStr: "parameter time SIM_TIME = 100ns",
			expectedParams: []*Parameter{
				{Name: "SIM_TIME", Type: TIME, DefaultValue: "100ns", AnsiStyle: true},
			},
		},
		{
			name:         "Parameter with type and signed-unsigned (type captures base)",
			paramListStr: "parameter integer unsigned MAX_COUNT = 100",
			expectedParams: []*Parameter{
				{Name: "MAX_COUNT", Type: INTEGER, DefaultValue: "100", AnsiStyle: true},
			}, // Regex captures 'integer' as type
		},
		{
			name:         "Single parameter no type no default",
			paramListStr: "WIDTH",
			expectedParams: []*Parameter{
				{Name: "WIDTH", Type: LOGIC, DefaultValue: "", AnsiStyle: true},
			},
		},
		{
			name:         "Single parameter with default value",
			paramListStr: "WIDTH = 8",
			expectedParams: []*Parameter{
				{Name: "WIDTH", Type: INTEGER, DefaultValue: "8", AnsiStyle: true},
			},
		},
		{
			name:         "Single parameter with type and default value",
			paramListStr: "parameter int DATA_WIDTH = 32",
			expectedParams: []*Parameter{
				{Name: "DATA_WIDTH", Type: INT, DefaultValue: "32", AnsiStyle: true},
			},
		},
		{
			name:         "Single parameter with type no default",
			paramListStr: "parameter logic CLK_PERIOD",
			expectedParams: []*Parameter{
				{Name: "CLK_PERIOD", Type: LOGIC, DefaultValue: "", AnsiStyle: true},
			},
		},
		{
			name:         "Type",
			paramListStr: "parameter type P_TYPE = logic",
			expectedParams: []*Parameter{
				{Name: "P_TYPE", Type: TYPE, DefaultValue: "logic", AnsiStyle: true},
			},
		},
		{
			name:         "param with width",
			paramListStr: "parameter logic [7:0] P_SIZED = 8'hAA",
			expectedParams: []*Parameter{
				{Name: "P_SIZED", Type: LOGIC, DefaultValue: "8'hAA", Width: 8, AnsiStyle: true},
			},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			params, err := parseParameters(tc.paramListStr, true)
			if err != nil {
				t.Fatalf("parseParameters() error = %v", err)
			}

			// sort the parameters by name for consistent comparison
			sort.Slice(params, func(i, j int) bool {
				return params[i].Name < params[j].Name
			})
			sort.Slice(tc.expectedParams, func(i, j int) bool {
				return tc.expectedParams[i].Name < tc.expectedParams[j].Name
			})
			if !reflect.DeepEqual(params, tc.expectedParams) {
				t.Errorf("parseParameters() = %v, want %v", params, tc.expectedParams)
				// Detailed comparison
				if len(params) != len(tc.expectedParams) {
					t.Errorf(
						"Length mismatch: got %d, want %d",
						len(params),
						len(tc.expectedParams),
					)
				} else {
					for i := range params {
						if !reflect.DeepEqual(params[i], tc.expectedParams[i]) {
							t.Errorf("Mismatch at index %d: got %+v, want %+v", i, params[i], tc.expectedParams[i])
						}
					}
				}
			}
		})
	}
}

func TestParseNonANSIParameterDeclarations(t *testing.T) {
	testCases := []struct {
		name           string
		content        string
		expectedModule *Module
		expectError    bool
	}{
		{
			name: "Non-ANSI parameter declarations in module body",
			content: `
module non_ansi_params (
    input clk,
    input rst,
    output [WIDTH-1:0] data_out
);
    parameter WIDTH = 8;
    parameter DEPTH = 16;
    parameter logic [3:0] CONTROL = 4'b1010;
    localparam ADDR_WIDTH = $clog2(DEPTH);
    
    reg [WIDTH-1:0] internal_reg;
    always @(posedge clk) begin
        internal_reg <= internal_reg + 1;
    end
    assign data_out = internal_reg;
endmodule
`,
			expectedModule: &Module{
				Name: "non_ansi_params",
				Ports: []*Port{
					{Name: "clk", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
					{Name: "rst", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
					{Name: "data_out", Direction: OUTPUT, Type: LOGIC, Width: 8, IsSigned: false},
				},
				Parameters: []*Parameter{
					{Name: "WIDTH", Type: INTEGER, DefaultValue: "8", AnsiStyle: false},
					{Name: "DEPTH", Type: INTEGER, DefaultValue: "16", AnsiStyle: false},
					{
						Name:         "CONTROL",
						Type:         LOGIC,
						DefaultValue: "4'b1010",
						Width:        4,
						AnsiStyle:    false,
					},
					{
						Name:         "ADDR_WIDTH",
						Type:         UNKNOWN,
						DefaultValue: "$clog2(DEPTH)",
						Localparam:   true,
						AnsiStyle:    false,
					},
				},
				Body:      "\n    parameter WIDTH = 8;\n    parameter DEPTH = 16;\n    parameter logic [3:0] CONTROL = 4'b1010;\n    localparam ADDR_WIDTH = $clog2(DEPTH);\n    \n    reg [WIDTH-1:0] internal_reg;\n    always @(posedge clk) begin\n        internal_reg <= internal_reg + 1;\n    end\n    assign data_out = internal_reg;\n",
				AnsiStyle: false,
			},
			expectError: false,
		},
		{
			name: "Mixed ANSI and non-ANSI parameters",
			content: `
module mixed_params #(
    parameter INIT_VALUE = 0
) (
    input clk,
    output [DATA_WIDTH-1:0] result
);
    parameter DATA_WIDTH = 32;
    localparam MAX_COUNT = 2**DATA_WIDTH - 1;
    
    reg [DATA_WIDTH-1:0] counter;
    assign result = counter;
endmodule
`,
			expectedModule: &Module{
				Name: "mixed_params",
				Ports: []*Port{
					{Name: "clk", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
					{Name: "result", Direction: OUTPUT, Type: LOGIC, Width: 32, IsSigned: false},
				},
				Parameters: []*Parameter{
					{Name: "INIT_VALUE", Type: LOGIC, DefaultValue: "0", AnsiStyle: true},
					{Name: "DATA_WIDTH", Type: INTEGER, DefaultValue: "32", AnsiStyle: false},
					{
						Name:         "MAX_COUNT",
						Type:         UNKNOWN,
						DefaultValue: "2**DATA_WIDTH - 1",
						Localparam:   true,
						AnsiStyle:    false,
					},
				},
				Body:      "\n    parameter DATA_WIDTH = 32;\n    localparam MAX_COUNT = 2**DATA_WIDTH - 1;\n    \n    reg [DATA_WIDTH-1:0] counter;\n    assign result = counter;\n",
				AnsiStyle: false,
			},
			expectError: false,
		},
		{
			name: "Only non-ANSI parameters with types",
			content: `
module typed_params (
    input enable,
    output valid
);
    parameter integer TIMEOUT = 1000;
    parameter real FREQUENCY = 100.5;
    parameter string MODE = "FAST";
    parameter time DELAY = 10ns;
    
    assign valid = enable;
endmodule
`,
			expectedModule: &Module{
				Name: "typed_params",
				Ports: []*Port{
					{Name: "enable", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
					{Name: "valid", Direction: OUTPUT, Type: LOGIC, Width: 0, IsSigned: false},
				},
				Parameters: []*Parameter{
					{Name: "TIMEOUT", Type: INTEGER, DefaultValue: "1000", AnsiStyle: false},
					{Name: "FREQUENCY", Type: REAL, DefaultValue: "100.5", AnsiStyle: false},
					{Name: "MODE", Type: STRING, DefaultValue: `"FAST"`, AnsiStyle: false},
					{Name: "DELAY", Type: TIME, DefaultValue: "10ns", AnsiStyle: false},
				},
				Body:      "\n    parameter integer TIMEOUT = 1000;\n    parameter real FREQUENCY = 100.5;\n    parameter string MODE = \"FAST\";\n    parameter time DELAY = 10ns;\n    \n    assign valid = enable;\n",
				AnsiStyle: false,
			},
			expectError: false,
		},
		{
			name: "Parameter redefinition - body overrides header",
			content: `
module param_override #(
    parameter WIDTH = 4,
    parameter TYPE_PARAM = 16
) (
    input [WIDTH-1:0] data_in,
    output [WIDTH-1:0] data_out
);
    parameter WIDTH = 8; // Override header value
    parameter integer BODY_ONLY = 42;
    
    assign data_out = data_in;
endmodule
`,
			expectedModule: &Module{
				Name: "param_override",
				Ports: []*Port{
					{Name: "data_in", Direction: INPUT, Type: LOGIC, Width: 8, IsSigned: false},
					{Name: "data_out", Direction: OUTPUT, Type: LOGIC, Width: 8, IsSigned: false},
				},
				Parameters: []*Parameter{
					{
						Name:         "WIDTH",
						Type:         INTEGER,
						DefaultValue: "8",
						AnsiStyle:    false,
					}, // Body value wins
					{
						Name:         "TYPE_PARAM",
						Type:         INTEGER,
						DefaultValue: "16",
						AnsiStyle:    true,
					}, // Header only
					{
						Name:         "BODY_ONLY",
						Type:         INTEGER,
						DefaultValue: "42",
						AnsiStyle:    false,
					}, // Body only
				},
				Body:      "\n    parameter WIDTH = 8; \n    parameter integer BODY_ONLY = 42;\n    \n    assign data_out = data_in;\n",
				AnsiStyle: false,
			},
			expectError: false,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			vfile, err := ParseVerilog(tc.content, 0)

			hasError := (err != nil)
			if hasError != tc.expectError {
				t.Fatalf("ParseVerilog() error = %v, expectError %v", err, tc.expectError)
			}

			if tc.expectError {
				return
			}

			if vfile == nil {
				t.Fatalf("ParseVerilog() returned nil VerilogFile, expected non-nil")
			}

			parsedModule, ok := vfile.Modules[tc.expectedModule.Name]
			if !ok {
				t.Fatalf(
					"Module '%s' not found in parsed VerilogFile.Modules. Found: %+v",
					tc.expectedModule.Name,
					vfile.Modules,
				)
			}

			// Compare parameters
			if !reflect.DeepEqual(parsedModule.Parameters, tc.expectedModule.Parameters) {
				t.Errorf(
					"Parameters mismatch:\nGot: %+v\nWant: %+v",
					parsedModule.Parameters,
					tc.expectedModule.Parameters,
				)
				// Detailed parameter comparison
				for i, expected := range tc.expectedModule.Parameters {
					if i < len(parsedModule.Parameters) {
						actual := parsedModule.Parameters[i]
						if reflect.DeepEqual(actual, expected) {
							continue
						}
						if actual.Name != expected.Name {
							t.Errorf(
								"Parameter %d name mismatch: got %s, want %s",
								i,
								actual.Name,
								expected.Name,
							)
						}
						if actual.AnsiStyle != expected.AnsiStyle {
							t.Errorf(
								"Parameter %s AnsiStyle mismatch: got %v, want %v",
								actual.Name,
								actual.AnsiStyle,
								expected.AnsiStyle,
							)
						}
						if actual.Type != expected.Type {
							t.Errorf(
								"Parameter %s Type mismatch: got %s, want %s",
								actual.Name,
								actual.Type,
								expected.Type,
							)
						}
						if actual.DefaultValue != expected.DefaultValue {
							t.Errorf(
								"Parameter %s DefaultValue mismatch: got %s, want %s",
								actual.Name,
								actual.DefaultValue,
								expected.DefaultValue,
							)
						}
						if actual.Width != expected.Width {
							t.Errorf(
								"Parameter %s Width mismatch: got %d, want %d",
								actual.Name,
								actual.Width,
								expected.Width,
							)
						}
						if actual.Localparam != expected.Localparam {
							t.Errorf(
								"Parameter %s Localparam mismatch: got %v, want %v",
								actual.Name,
								actual.Localparam,
								expected.Localparam,
							)
						}
					} else {
						t.Errorf(
							"Missing parameter at index %d: expected %+v, got nothing",
							i,
							expected,
						)
					}
				}
			}

			// Compare ports (simplified check)
			if len(parsedModule.Ports) != len(tc.expectedModule.Ports) {
				t.Errorf(
					"Port count mismatch: got %d, want %d",
					len(parsedModule.Ports),
					len(tc.expectedModule.Ports),
				)
			}

			// Check that module is marked as non-ANSI style
			/*
				if parsedModule.AnsiStyle != tc.expectedModule.AnsiStyle {
					t.Errorf(
						"AnsiStyle mismatch: got %v, want %v",
						parsedModule.AnsiStyle,
						tc.expectedModule.AnsiStyle,
					)
				}
			*/
		})
	}
}

func TestSplitParametersSmart(t *testing.T) {
	testCases := []struct {
		name     string
		input    string
		expected []string
	}{
		{
			name:     "Simple parameters",
			input:    "A = 1, B = 2, C = 3",
			expected: []string{"A = 1", " B = 2", " C = 3"},
		},
		{
			name:     "Empty string",
			input:    "",
			expected: []string{},
		},
		{
			name:     "Single parameter",
			input:    "WIDTH = 8",
			expected: []string{"WIDTH = 8"},
		},
		{
			name:     "Parameter with ternary operator",
			input:    "A = (x ? 1 : 2), B = 3",
			expected: []string{"A = (x ? 1 : 2)", " B = 3"},
		},
		{
			name:     "Parameter with nested parentheses",
			input:    "A = ((x + y) * (z ? 1 : 2)), B = simple",
			expected: []string{"A = ((x + y) * (z ? 1 : 2))", " B = simple"},
		},
		{
			name:     "Parameter with concatenation",
			input:    "A = {a, b, c}, B = simple",
			expected: []string{"A = {a, b, c}", " B = simple"},
		},
		{
			name:  "Complex verismith-style parameter",
			input: "param84 = ((8'ha8) ? {(~&(((8'h9f) * (8'hbc)) ? ((8'hb7) ^~ (8'hbd)) : ((8'hbd) == (7'h44)))), {((~&(7'h41)) == (!(8'hb6)))}} : (((((7'h40) <= (8'xa3)) << (~|(8'hb7))) ? (((8'hac) != (8'hba)) | (8'h9e)) : (((8'hac) ~^ (8'hbd)) ? ((8'haa) ? (8'hbd) : (8'hae)) : (^(8'ha1)))) & ((((8'ha9) && (8'hb8)) * (|(7'h44))) ? ({(8'hbd), (8'h9e)} <<< ((7'h43) < (8'hb9))) : {((8'hae) ? (8'hbb) : (8'ha7))}))), param85 = simple",
			expected: []string{
				"param84 = ((8'ha8) ? {(~&(((8'h9f) * (8'hbc)) ? ((8'hb7) ^~ (8'hbd)) : ((8'hbd) == (7'h44)))), {((~&(7'h41)) == (!(8'hb6)))}} : (((((7'h40) <= (8'xa3)) << (~|(8'hb7))) ? (((8'hac) != (8'hba)) | (8'h9e)) : (((8'hac) ~^ (8'hbd)) ? ((8'haa) ? (8'hbd) : (8'hae)) : (^(8'ha1)))) & ((((8'ha9) && (8'hb8)) * (|(7'h44))) ? ({(8'hbd), (8'h9e)} <<< ((7'h43) < (8'hb9))) : {((8'hae) ? (8'hbb) : (8'ha7))})))",
				" param85 = simple",
			},
		},
		{
			name:     "Parameter with string containing comma",
			input:    `A = "hello, world", B = 42`,
			expected: []string{`A = "hello, world"`, " B = 42"},
		},
		{
			name:     "Parameter with array indices",
			input:    "A = array[1,2], B = simple",
			expected: []string{"A = array[1,2]", " B = simple"},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			result := splitParametersSmart(tc.input)

			if len(result) != len(tc.expected) {
				t.Errorf("Length mismatch: got %d, want %d", len(result), len(tc.expected))
				t.Errorf("Got: %v", result)
				t.Errorf("Want: %v", tc.expected)
				return
			}

			for i, expected := range tc.expected {
				if result[i] != expected {
					t.Errorf("Parameter %d mismatch: got %q, want %q", i, result[i], expected)
				}
			}
		})
	}
}
