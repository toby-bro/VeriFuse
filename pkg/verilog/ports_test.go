package verilog

import (
	"reflect"
	"testing"
)

func TestParsePortDeclaration(t *testing.T) {
	testCases := []struct {
		name         string
		line         string
		expectedPort *Port

		expectedOK bool
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
		{
			name: "Port with verilator public pragma",
			line: "(* verilator public *) output logic [7:0] public_output_wire;",
			expectedPort: &Port{
				Name:      "public_output_wire",
				Direction: OUTPUT,
				Type:      LOGIC,
				Width:     8,
				IsSigned:  false,
				Pragma:    "verilator public",
			},
			expectedOK: true,
		},
		{
			name: "Port with wire_force_assign pragma",
			line: "(* wire_force_assign *) input logic forced_internal_in;",
			expectedPort: &Port{
				Name:      "forced_internal_in",
				Direction: INPUT,
				Type:      LOGIC,
				Width:     0,
				IsSigned:  false,
				Pragma:    "wire_force_assign",
			},
			expectedOK: true,
		},
		{
			name: "Port with wire_force_release pragma",
			line: "(* wire_force_release *) output logic forced_internal_out;",
			expectedPort: &Port{
				Name:      "forced_internal_out",
				Direction: OUTPUT,
				Type:      LOGIC,
				Width:     0,
				IsSigned:  false,
				Pragma:    "wire_force_release",
			},
			expectedOK: true,
		},
		{
			name: "Port with pragma and range",
			line: "(* verilator public *) input wire [31:0] pragma_with_range;",
			expectedPort: &Port{
				Name:      "pragma_with_range",
				Direction: INPUT,
				Type:      WIRE,
				Width:     32,
				IsSigned:  false,
				Pragma:    "verilator public",
			},
			expectedOK: true,
		},
		{
			name: "Port with pragma and signed",
			line: "(* custom_pragma *) input reg signed [15:0] pragma_signed;",
			expectedPort: &Port{
				Name:      "pragma_signed",
				Direction: INPUT,
				Type:      REG,
				Width:     16,
				IsSigned:  true,
				Pragma:    "custom_pragma",
			},
			expectedOK: true,
		},
		{
			name: "Port with multi-word pragma",
			line: "(* verilator lint_off WIDTH *) output logic [7:0] multi_word_pragma;",
			expectedPort: &Port{
				Name:      "multi_word_pragma",
				Direction: OUTPUT,
				Type:      LOGIC,
				Width:     8,
				IsSigned:  false,
				Pragma:    "verilator lint_off WIDTH",
			},
			expectedOK: true,
		},
		{
			name: "Port with pragma containing equals",
			line: "(* keep = \"true\" *) input bit keep_signal;",
			expectedPort: &Port{
				Name:      "keep_signal",
				Direction: INPUT,
				Type:      BIT,
				Width:     0,
				IsSigned:  false,
				Pragma:    "keep = \"true\"",
			},
			expectedOK: true,
		},
	}

	// Create an empty parameters map for testing
	emptyParams := make(map[string]*Parameter)

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			// Pass emptyParams to the function
			port, ok := parsePortDeclaration(tc.line, emptyParams, nil)

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

func TestExtractANSIPortDeclarations(t *testing.T) {
	// Define common parameters for testing
	testParams := map[string]*Parameter{
		"WIDTH":      {Name: "WIDTH", DefaultValue: "8"},
		"DATA_WIDTH": {Name: "DATA_WIDTH", DefaultValue: "32"},
		"ADDR_BUS":   {Name: "ADDR_BUS", DefaultValue: "16"},
	}

	testCases := []struct {
		name              string
		portListStr       string
		parameters        map[string]*Parameter
		expectedPortsMap  map[string]*Port
		expectedPortOrder []string
	}{
		{
			name:              "Empty port list",
			portListStr:       "",
			parameters:        nil,
			expectedPortsMap:  map[string]*Port{},
			expectedPortOrder: []string{},
		},
		{
			name:        "Extra whitespace",
			portListStr: "  input   logic   [ 3 : 0 ]   spaced_out  , output wire normal_out",
			parameters:  nil,
			expectedPortsMap: map[string]*Port{
				"spaced_out": {
					Name:      "spaced_out",
					Direction: INPUT,
					Type:      LOGIC,
					Width:     4,
					IsSigned:  false,
				},
				"normal_out": {
					Name:      "normal_out",
					Direction: OUTPUT,
					Type:      WIRE,
					Width:     0,
					IsSigned:  false,
				},
			},
			expectedPortOrder: []string{"spaced_out", "normal_out"},
		},
		{
			name:        "Inout wire signed with range",
			portListStr: "inout wire signed [15:0] addr",
			parameters:  nil,
			expectedPortsMap: map[string]*Port{
				"addr": {Name: "addr", Direction: INOUT, Type: WIRE, Width: 16, IsSigned: true},
			},
			expectedPortOrder: []string{"addr"},
		},
		{
			name:        "Input logic with trailing comma",
			portListStr: "input logic clk,",
			parameters:  nil,
			expectedPortsMap: map[string]*Port{
				"clk": {Name: "clk", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
			},
			expectedPortOrder: []string{"clk"},
		},
		{
			name:              "Malformed - missing name",
			portListStr:       "input logic [7:0]",
			parameters:        nil,
			expectedPortsMap:  map[string]*Port{}, // Should not parse
			expectedPortOrder: []string{},
		},
		{
			name:        "Mixed ANSI and simple names",
			portListStr: "input logic start, stop, output [7:0] result",
			parameters:  nil,
			expectedPortsMap: map[string]*Port{
				"start": {Name: "start", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
				"stop": {
					Name:      "stop",
					Direction: INPUT,
					Type:      LOGIC,
					Width:     0,
					IsSigned:  false,
				}, // Parsed as simple name
				"result": {
					Name:      "result",
					Direction: OUTPUT,
					Type:      LOGIC,
					Width:     8,
					IsSigned:  false,
				}, // Type UNKNOWN as 'logic' not with it
			},
			// The regex for ANSI ports is greedy. "output [7:0] result" will be matched.
			// "stop" will be parsed by the simplePortRegex.
			// "input logic start" is a full ANSI match.
			// The order depends on how split and regex matching proceeds.
			// Current `extractANSIPortDeclarations` logic might process "input logic start", then "stop", then "output [7:0] result"
			// Let's adjust expected order based on typical processing.
			expectedPortOrder: []string{"start", "stop", "result"},
		},
		{
			name:        "Multiple ports",
			portListStr: "input logic rst_n, output reg [3:0] count, input ena",
			parameters:  nil,
			expectedPortsMap: map[string]*Port{
				"rst_n": {Name: "rst_n", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
				"count": {Name: "count", Direction: OUTPUT, Type: REG, Width: 4, IsSigned: false},
				"ena": {
					Name:      "ena",
					Direction: INPUT,
					Type:      LOGIC,
					Width:     0,
					IsSigned:  false,
				},
			},
			expectedPortOrder: []string{"rst_n", "count", "ena"},
		},
		{
			name:        "Output logic with range",
			portListStr: "output logic [7:0] data_out",
			parameters:  nil,
			expectedPortsMap: map[string]*Port{
				"data_out": {
					Name:      "data_out",
					Direction: OUTPUT,
					Type:      LOGIC,
					Width:     8,
					IsSigned:  false,
				},
			},
			expectedPortOrder: []string{"data_out"},
		},
		{
			name:        "Parameterized width",
			portListStr: "input logic [WIDTH-1:0] param_in",
			parameters:  testParams,
			expectedPortsMap: map[string]*Port{
				"param_in": {
					Name:      "param_in",
					Direction: INPUT,
					Type:      LOGIC,
					Width:     8,
					IsSigned:  false,
				},
			},
			expectedPortOrder: []string{"param_in"},
		},
		{
			name:        "Parameterized width ADDR_BUS direct",
			portListStr: "input [ADDR_BUS:0] address", // Note: [PARAM:0] style
			parameters:  testParams,
			expectedPortsMap: map[string]*Port{
				"address": {
					Name:      "address",
					Direction: INPUT,
					Type:      LOGIC,
					Width:     17,
					IsSigned:  false,
				}, // Type UNKNOWN as it's not specified with keyword
			},
			expectedPortOrder: []string{"address"},
		},
		{
			name:        "Parameterized width DATA_WIDTH",
			portListStr: "output logic [DATA_WIDTH-1:0] data_bus",
			parameters:  testParams,
			expectedPortsMap: map[string]*Port{
				"data_bus": {
					Name:      "data_bus",
					Direction: OUTPUT,
					Type:      LOGIC,
					Width:     32,
					IsSigned:  false,
				},
			},
			expectedPortOrder: []string{"data_bus"},
		},
		{
			name:        "Port with dot notation (interface style, parsed as simple name)",
			portListStr: ".clk(clock_signal), .rst(reset_signal)",
			parameters:  nil,
			expectedPortsMap: map[string]*Port{
				// The regex `simplePortRegex` captures the name before the parenthesis as the port name
				"clk": {Name: "clk", Direction: INTERNAL, Type: UNKNOWN, Width: 0, IsSigned: false},
				"rst": {Name: "rst", Direction: INTERNAL, Type: UNKNOWN, Width: 0, IsSigned: false},
			},
			expectedPortOrder: []string{"clk", "rst"},
		},
		{
			name:        "Port with type 'bit'",
			portListStr: "output bit error_flag",
			parameters:  nil,
			expectedPortsMap: map[string]*Port{
				"error_flag": {
					Name:      "error_flag",
					Direction: OUTPUT,
					Type:      BIT,
					Width:     0,
					IsSigned:  false,
				},
			},
			expectedPortOrder: []string{"error_flag"},
		},
		{
			name:        "Port with type 'byte' and signed",
			portListStr: "input byte signed control_byte",
			parameters:  nil,
			expectedPortsMap: map[string]*Port{
				"control_byte": {
					Name:      "control_byte",
					Direction: INPUT,
					Type:      BYTE,
					Width:     0,
					IsSigned:  true,
				},
			},
			expectedPortOrder: []string{"control_byte"},
		},
		{
			name:        "Port with type 'int'",
			portListStr: "input int counter_val",
			parameters:  nil,
			expectedPortsMap: map[string]*Port{
				"counter_val": {
					Name:      "counter_val",
					Direction: INPUT,
					Type:      INT,
					Width:     0,
					IsSigned:  false,
				},
			},
			expectedPortOrder: []string{"counter_val"},
		},
		{
			name:        "Simple input logic",
			portListStr: "input logic clk",
			parameters:  nil,
			expectedPortsMap: map[string]*Port{
				"clk": {Name: "clk", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
			},
			expectedPortOrder: []string{"clk"},
		},
		{
			name:              "Simple port names (non-ANSI in header style)",
			portListStr:       "clk, rst, data",
			parameters:        nil,
			expectedPortsMap:  map[string]*Port{},
			expectedPortOrder: []string{},
		},
		{
			name:        "simple array",
			portListStr: "input logic [7:0] data_array[4]",
			parameters:  nil,
			expectedPortsMap: map[string]*Port{
				"data_array": {
					Name:      "data_array",
					Direction: INPUT,
					Type:      LOGIC,
					Width:     8,
					IsSigned:  false,
					Array:     "4",
				},
			},
			expectedPortOrder: []string{"data_array"},
		},
		{
			name:        "Port with verilator public pragma",
			portListStr: "(* verilator public *) output logic [7:0] public_wire",
			parameters:  nil,
			expectedPortsMap: map[string]*Port{
				"public_wire": {
					Name:      "public_wire",
					Direction: OUTPUT,
					Type:      LOGIC,
					Width:     8,
					IsSigned:  false,
					Pragma:    "verilator public",
				},
			},
			expectedPortOrder: []string{"public_wire"},
		},
		{
			name:        "Multiple ports with pragmas",
			portListStr: "(* verilator public *) input logic clk, (* wire_force_assign *) output wire [3:0] data",
			parameters:  nil,
			expectedPortsMap: map[string]*Port{
				"clk": {
					Name:      "clk",
					Direction: INPUT,
					Type:      LOGIC,
					Width:     0,
					IsSigned:  false,
					Pragma:    "verilator public",
				},
				"data": {
					Name:      "data",
					Direction: OUTPUT,
					Type:      WIRE,
					Width:     4,
					IsSigned:  false,
					Pragma:    "wire_force_assign",
				},
			},
			expectedPortOrder: []string{"clk", "data"},
		},
		{
			name:        "Port with pragma and parameterized width",
			portListStr: "(* custom_attr = \"value\" *) input logic [WIDTH-1:0] param_port",
			parameters:  testParams,
			expectedPortsMap: map[string]*Port{
				"param_port": {
					Name:      "param_port",
					Direction: INPUT,
					Type:      LOGIC,
					Width:     8,
					IsSigned:  false,
					Pragma:    "custom_attr = \"value\"",
				},
			},
			expectedPortOrder: []string{"param_port"},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			portsMap, portOrder := extractANSIPortDeclarations(tc.portListStr, tc.parameters)

			if !reflect.DeepEqual(portsMap, tc.expectedPortsMap) {
				t.Errorf(
					"extractANSIPortDeclarations() portsMap = %+v, want %+v",
					portsMap,
					tc.expectedPortsMap,
				)
				// Log detailed differences for easier debugging
				for k, expectedV := range tc.expectedPortsMap {
					actualV, ok := portsMap[k]
					if !ok {
						t.Errorf("Missing port in map: %s", k)
						continue
					}
					if !reflect.DeepEqual(actualV, expectedV) {
						t.Errorf("Port '%s' mismatch: got %+v, want %+v", k, actualV, expectedV)
					}
				}
				for k := range portsMap {
					if _, ok := tc.expectedPortsMap[k]; !ok {
						t.Errorf("Extra port in map: %s", k)
					}
				}
			}

			if !reflect.DeepEqual(portOrder, tc.expectedPortOrder) {
				t.Errorf(
					"extractANSIPortDeclarations() portOrder = %v, want %v",
					portOrder,
					tc.expectedPortOrder,
				)
			}
		})
	}
}

func TestExtractNonANSIPortDeclarations(t *testing.T) {
	// Define common parameters for testing
	testParams := map[string]*Parameter{
		"P_WIDTH":    {Name: "P_WIDTH", DefaultValue: "8"},
		"DATA_SIZE":  {Name: "DATA_SIZE", DefaultValue: "32"},
		"ADDR_LINES": {Name: "ADDR_LINES", DefaultValue: "16"},
	}

	testCases := []struct {
		name             string
		content          string
		parameters       map[string]*Parameter
		expectedPortsMap map[string]*Port
		expectError      bool
	}{
		{
			name: "Content with only comments",
			content: `// This is a comment
/* This is a
   multi-line comment */
wire clk; // Not a port declaration`,
			parameters:       nil,
			expectedPortsMap: map[string]*Port{},
			expectError:      false,
		},
		{
			name:             "Empty content",
			content:          "",
			parameters:       nil,
			expectedPortsMap: map[string]*Port{},
			expectError:      false,
		},
		{
			name: "Malformed port declaration - no name (should be skipped by parsePortDeclaration)",
			content: `
input logic [7:0];
output valid_out;
`,
			parameters: nil,
			expectedPortsMap: map[string]*Port{
				"valid_out": {
					Name:      "valid_out",
					Direction: OUTPUT,
					Type:      LOGIC,
					Width:     0,
					IsSigned:  false,
				},
			},
			expectError: false,
		},
		{
			name: "Mixed valid and invalid lines",
			content: `
// Start of module
input clk;
wire internal_signal; // Not a port
output [7:0] data;
/*
module another_module (
    input x
);
endmodule
*/
inout control_sig;
`,
			parameters: nil,
			expectedPortsMap: map[string]*Port{
				"clk": {
					Name:      "clk",
					Direction: INPUT,
					Type:      LOGIC,
					Width:     0,
					IsSigned:  false,
				}, // Default type LOGIC, width 1
				"data": {
					Name:      "data",
					Direction: OUTPUT,
					Type:      LOGIC,
					Width:     8,
					IsSigned:  false,
				}, // Default type LOGIC
				"control_sig": {
					Name:      "control_sig",
					Direction: INOUT,
					Type:      LOGIC,
					Width:     0,
					IsSigned:  false,
				}, // Default type LOGIC, width 1
			},
			expectError: false,
		},
		{
			name: "Multiple valid port declarations",
			content: `
input rst_n;
output logic [3:0] count;
input wire ena;`,
			parameters: nil,
			expectedPortsMap: map[string]*Port{
				"rst_n": {
					Name:      "rst_n",
					Direction: INPUT,
					Type:      LOGIC,
					Width:     0,
					IsSigned:  false,
				}, // Default type LOGIC, width 1
				"count": {Name: "count", Direction: OUTPUT, Type: LOGIC, Width: 4, IsSigned: false},
				"ena": {
					Name:      "ena",
					Direction: INPUT,
					Type:      WIRE,
					Width:     0,
					IsSigned:  false,
				}, // Width 1
			},
			expectError: false,
		},
		{
			name: "Parameterized port width direct ADDR_LINES",
			content: `
input [ADDR_LINES:0] address; // Note: [PARAM:0] style
`,
			parameters: testParams,
			expectedPortsMap: map[string]*Port{
				"address": {
					Name:      "address",
					Direction: INPUT,
					Type:      LOGIC,
					Width:     17,
					IsSigned:  false,
				}, // Default type LOGIC
			},
			expectError: false,
		},
		{
			name: "Parameterized port widths",
			content: `
input [P_WIDTH-1:0] param_in;
output logic [DATA_SIZE-1:0] data_bus;
`,
			parameters: testParams,
			expectedPortsMap: map[string]*Port{
				"param_in": {
					Name:      "param_in",
					Direction: INPUT,
					Type:      LOGIC,
					Width:     8,
					IsSigned:  false,
				}, // Default type LOGIC
				"data_bus": {
					Name:      "data_bus",
					Direction: OUTPUT,
					Type:      LOGIC,
					Width:     32,
					IsSigned:  false,
				},
			},
			expectError: false,
		},
		{
			name: "Port declared multiple times (first wins)",
			content: `
input logic [7:0] data;
output reg [7:0] data; // This should be ignored for 'data'
`,
			parameters: nil,
			expectedPortsMap: map[string]*Port{
				"data": {Name: "data", Direction: INPUT, Type: LOGIC, Width: 8, IsSigned: false},
			},
			expectError: false,
		},
		{
			name: "Port with type 'bit' and comment",
			content: `
output bit error_flag; // This is an error flag
`,
			parameters: nil,
			expectedPortsMap: map[string]*Port{
				"error_flag": {
					Name:      "error_flag",
					Direction: OUTPUT,
					Type:      BIT,
					Width:     0,
					IsSigned:  false,
				},
			},
			expectError: false,
		},
		{
			name: "Port with type 'byte' and signed, extra whitespace",
			content: `
  input  byte  signed   control_byte  ;
`,
			parameters: nil,
			expectedPortsMap: map[string]*Port{
				"control_byte": {
					Name:      "control_byte",
					Direction: INPUT,
					Type:      BYTE,
					Width:     0,
					IsSigned:  true,
				},
			},
			expectError: false,
		},
		{
			name: "Port with type 'int'",
			content: `
input int counter_val;
`,
			parameters: nil,
			expectedPortsMap: map[string]*Port{
				"counter_val": {
					Name:      "counter_val",
					Direction: INPUT,
					Type:      INT,
					Width:     0,
					IsSigned:  false,
				},
			},
			expectError: false,
		},
		{
			name:       "Single inout port signed with range",
			content:    "inout wire signed [15:0] addr_bus;",
			parameters: nil,
			expectedPortsMap: map[string]*Port{
				"addr_bus": {
					Name:      "addr_bus",
					Direction: INOUT,
					Type:      WIRE,
					Width:     16,
					IsSigned:  true,
				},
			},
			expectError: false,
		},
		{
			name:       "Single input port",
			content:    "input logic clk;",
			parameters: nil,
			expectedPortsMap: map[string]*Port{
				"clk": {Name: "clk", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
			},
			expectError: false,
		},
		{
			name:       "Single output port with range",
			content:    "output reg [7:0] data_out;",
			parameters: nil,
			expectedPortsMap: map[string]*Port{
				"data_out": {
					Name:      "data_out",
					Direction: OUTPUT,
					Type:      REG,
					Width:     8,
					IsSigned:  false,
				},
			},
			expectError: false,
		},
		{
			name:       "weirdWidths",
			content:    "input wire [(1'h0):(1'h0)] clk;",
			parameters: nil,
			expectedPortsMap: map[string]*Port{
				"clk": {
					Name:      "clk",
					Direction: INPUT,
					Type:      WIRE,
					Width:     1,
					IsSigned:  false,
				},
			},
			expectError: false,
		},
		{
			name: "No port buf function declaration",
			content: `
	function automatic bit [4:0] add_saturate;
        input bit [3:0] op1;
        input bit [3:0] op2;
        bit [4:0] sum;
        //INJECT
        sum = {1'b0, op1} + {1'b0, op2};
        if (sum > 5'd15) sum = 5'd15;
        return sum;
        //INJECT
    endfunction
    //INJECT
    assign func_result = add_saturate(func_a, func_b);
    //INJECT
	`,
			parameters:       nil,
			expectedPortsMap: map[string]*Port{},
			expectError:      false,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			tc.content = cleanText(tc.content)
			portsMap, err := extractNonANSIPortDeclarations(tc.content, tc.parameters)

			if (err != nil) != tc.expectError {
				t.Fatalf(
					"extractNonANSIPortDeclarations() error = %v, expectError %v",
					err,
					tc.expectError,
				)
			}

			if !reflect.DeepEqual(portsMap, tc.expectedPortsMap) {
				t.Errorf(
					"extractNonANSIPortDeclarations() portsMap = %+v, want %+v",
					portsMap,
					tc.expectedPortsMap,
				)
				// Log detailed differences for easier debugging
				for k, expectedV := range tc.expectedPortsMap {
					actualV, ok := portsMap[k]
					if !ok {
						t.Errorf("Missing port in map: %s", k)
						continue
					}
					if !reflect.DeepEqual(actualV, expectedV) {
						t.Errorf("Port '%s' mismatch: got %+v, want %+v", k, actualV, expectedV)
					}
				}
				for k, actualV := range portsMap {
					if _, ok := tc.expectedPortsMap[k]; !ok {
						t.Errorf("Extra port in map: %s (value: %+v)", k, actualV)
					}
				}
			}
		})
	}
}
