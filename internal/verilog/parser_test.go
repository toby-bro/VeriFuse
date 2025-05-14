package verilog

import (
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"sort"
	"strings"
	"testing"

	"github.com/toby-bro/pfuzz/pkg/utils"
)

func TestMain(m *testing.M) {
	logger = utils.NewDebugLogger(5)
	exitCode := m.Run()
	os.Exit(exitCode)
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
		{"input wire [(1'h0):(1'h0)] clk;", "[(1'h0):(1'h0)]", nil, 1, false},
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

func TestParseVerilogLiteral(t *testing.T) {
	tests := []struct {
		name       string
		literalStr string
		wantVal    int64
		wantErr    bool
	}{
		// Valid Based Literals
		{"Hex simple", "'hFAB", 0xFAB, false},
		{"Hex with size", "12'hFAB", 0xFAB, false},
		{"Hex with underscores", "16'hF_A_B", 0xFAB, false},
		{"Binary simple", "'b1010", 10, false},
		{"Binary with size", "4'b1010", 10, false},
		{"Binary with underscores", "8'b1010_0101", 0xA5, false},
		{"Octal simple", "'o77", 0o77, false},
		{"Octal with size", "6'o77", 0o77, false},
		{"Octal with underscores", "9'o1_2_3", 0o123, false},
		{"Decimal based simple", "'d123", 123, false},
		{"Decimal based with size", "8'd123", 123, false},
		{"Decimal based with underscores", "10'd1_2_3", 123, false},
		{"Uppercase base H", "8'HF0", 0xF0, false},
		{"Uppercase base B", "4'B1100", 12, false},
		{"Uppercase base O", "6'O52", 42, false},
		{"Uppercase base D", "8'D99", 99, false},

		// Valid Simple Decimal Literals
		{"Simple decimal", "255", 255, false},
		{"Simple decimal with underscores", "1_000_000", 1000000, false},
		{"Zero", "0", 0, false},
		{"Negative simple decimal", "-10", -10, false}, // Assuming simple decimals can be negative

		// Invalid Inputs - Based Literals
		{"Invalid base char", "'xFAB", 0, true},
		{"Invalid hex value", "4'hG", 0, true},
		{"Invalid binary value", "2'b2", 0, true},
		{"Invalid octal value", "3'o8", 0, true},
		{"Invalid decimal based value", "4'dABC", 0, true},
		{"Missing value based", "'h", 0, true},
		{
			"Missing value based with size",
			"4'",
			0,
			true,
		}, // This will be caught by regex not matching

		// Invalid Inputs - Simple Decimal
		{"Non-numeric simple", "abc", 0, true},
		{"Mixed alpha-numeric simple", "1a2b", 0, true},

		// Edge cases
		{"Empty string", "", 0, true},
		{"Only underscores", "___", 0, true},
		{"Based literal too large for int64 (hex)", "65'hFFFFFFFFFFFFFFFFF", 0, true}, // > 64 bits

		// verismith
		{"Parenthesis", "(1'h0)", 0, false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			gotVal, err := parseVerilogLiteral(tt.literalStr)
			if (err != nil) != tt.wantErr {
				t.Errorf("parseVerilogLiteral() error = %v, wantErr %v", err, tt.wantErr)
				return
			}
			if !tt.wantErr && gotVal != tt.wantVal {
				t.Errorf("parseVerilogLiteral() gotVal = %v, want %v", gotVal, tt.wantVal)
			}
		})
	}
}

// Renamed from TestParseVerilogFile and updated for ParseVerilog
func TestParseVerilog(t *testing.T) {
	testCases := []struct {
		name                string
		content             string
		targetModuleName    string  // Used to identify the module to check in the result
		expectedModule      *Module // This is the module we expect to find in VerilogFile.Modules
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
			targetModuleName: "simple_adder",
			expectedModule: &Module{
				Name: "simple_adder",
				Ports: []Port{
					{Name: "a", Direction: INPUT, Type: LOGIC, Width: 8, IsSigned: false},
					{Name: "b", Direction: INPUT, Type: LOGIC, Width: 8, IsSigned: false},
					{Name: "sum", Direction: OUTPUT, Type: LOGIC, Width: 9, IsSigned: false},
				},
				Body:       "    assign sum = a + b;", // Expected body after parsing
				Parameters: []Parameter{},
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
			targetModuleName: "parameterized_module",
			expectedModule: &Module{
				Name: "parameterized_module",
				Ports: []Port{
					{Name: "in", Direction: INPUT, Type: LOGIC, Width: 8, IsSigned: false},
					{Name: "out", Direction: OUTPUT, Type: LOGIC, Width: 8, IsSigned: false},
				},
				Parameters: []Parameter{
					{
						Name:         "WIDTH",
						Type:         INTEGER,
						DefaultValue: "8",
					},
				},
				Body: "    assign out = in;", // Expected body after parsing
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
			targetModuleName:    "", // No specific module expected
			expectedModule:      nil,
			expectError:         false, // ParseVerilog itself might not error, but Modules map will be empty
			expectedErrorSubstr: "",    // No error string to check if expectError is false
		},
		{
			name:                "Empty File",
			content:             ``,
			targetModuleName:    "", // No specific module expected
			expectedModule:      nil,
			expectError:         false, // ParseVerilog itself might not error
			expectedErrorSubstr: "",    // No error string to check if expectError is false
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			// Call ParseVerilog with the content string and a default verbosity (e.g., 0)
			vfile, err := ParseVerilog(tc.content, 0)

			hasError := (err != nil)
			if hasError != tc.expectError {
				t.Fatalf("ParseVerilog() error = %v, expectError %v", err, tc.expectError)
			}

			if tc.expectError {
				if err != nil && tc.expectedErrorSubstr != "" &&
					!strings.Contains(err.Error(), tc.expectedErrorSubstr) {
					t.Errorf(
						"ParseVerilog() error = %q, expected substring %q",
						err,
						tc.expectedErrorSubstr,
					)
				}
				return // Don't check vfile content if an error was expected
			}

			// If no error was expected, vfile should be non-nil
			if vfile == nil {
				t.Fatalf("ParseVerilog() returned nil VerilogFile, expected non-nil")
			}

			if tc.expectedModule == nil { // Cases like "No Module Found" or "Empty File"
				if len(vfile.Modules) != 0 {
					t.Errorf(
						"Expected no modules, but got %d: %+v",
						len(vfile.Modules),
						vfile.Modules,
					)
				}
				if len(vfile.Classes) != 0 {
					t.Errorf(
						"Expected no classes, but got %d: %+v",
						len(vfile.Classes),
						vfile.Classes,
					)
				}
				if len(vfile.Structs) != 0 {
					t.Errorf(
						"Expected no structs, but got %d: %+v",
						len(vfile.Structs),
						vfile.Structs,
					)
				}
				return
			}

			// Check for the specific module
			parsedModule, ok := vfile.Modules[tc.targetModuleName]
			if !ok {
				t.Fatalf(
					"Module '%s' not found in parsed VerilogFile.Modules. Found: %+v",
					tc.targetModuleName,
					vfile.Modules,
				)
			}

			// Reorder the variable names by alphabetical order for comparison
			// This is a workaround for the fact that the order of variables in the parsed module
			// may not match the order in the original file.

			// Note: This is a simple approach and may not cover all cases.
			// A more robust solution would involve a deep comparison of the entire module structure.
			// Sort the Ports and Parameters by name
			sort.Slice(parsedModule.Ports, func(i, j int) bool {
				return parsedModule.Ports[i].Name < parsedModule.Ports[j].Name
			})

			// Compare the found module with the expected module
			// Note: The Body field in expectedModule must match the processed body from ParseVerilog
			if !reflect.DeepEqual(parsedModule, tc.expectedModule) {
				t.Errorf(
					"ParseVerilog() returned module does not match expected.\nReturned: %+v\nExpected: %+v",
					parsedModule,
					tc.expectedModule,
				)
				// Detailed diff (optional, for easier debugging)
				if parsedModule.Name != tc.expectedModule.Name {
					t.Errorf(
						"Name mismatch: got %s, want %s",
						parsedModule.Name,
						tc.expectedModule.Name,
					)
				}
				if !reflect.DeepEqual(parsedModule.Ports, tc.expectedModule.Ports) {
					t.Errorf(
						"Ports mismatch: got %+v, want %+v",
						parsedModule.Ports,
						tc.expectedModule.Ports,
					)
				}
				if !reflect.DeepEqual(parsedModule.Parameters, tc.expectedModule.Parameters) {
					t.Errorf(
						"Parameters mismatch: got %+v, want %+v",
						parsedModule.Parameters,
						tc.expectedModule.Parameters,
					)
				}
				if parsedModule.Body != tc.expectedModule.Body {
					t.Errorf(
						"Body mismatch: got %q, want %q",
						parsedModule.Body,
						tc.expectedModule.Body,
					)
				}
			}

			// For these specific test cases, we don't expect other structs or classes
			if len(vfile.Structs) != 0 {
				t.Errorf(
					"Expected no structs, but found %d: %+v",
					len(vfile.Structs),
					vfile.Structs,
				)
			}
			if len(vfile.Classes) != 0 {
				t.Errorf(
					"Expected no classes, but found %d: %+v",
					len(vfile.Classes),
					vfile.Classes,
				)
			}
		})
	}
}

var aa = `
rand logic [7:0] GGG_field1;
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
		{Name: "GGG_field2", Type: INT, Width: 0, Unsigned: true},
		{Name: "GGG_condition_var", Type: BIT, Width: 0, Unsigned: false},
		{
			Name:     "GGG_array_var",
			Type:     LOGIC,
			Width:    8,
			Unsigned: false,
		}, // Array attribute not checked here
		{Name: "GGG_index_limit", Type: INT, Width: 0, Unsigned: false},
		{
			Name:     "m_queue",
			Type:     INT,
			Width:    0,
			Unsigned: false,
		}, // Array attribute not checked here
		// For GGG_class_rand_var, ParseRange with nil parameters will default to width 8 for "[GGG_CLASS_WIDTH-1:0]"
		{Name: "GGG_class_rand_var", Type: LOGIC, Width: 8, Unsigned: false},
		{Name: "internal_wire", Type: LOGIC, Width: 8, Unsigned: false},
	}
	expectedTree := &ScopeNode{
		Level:     0,
		Parent:    nil,
		Variables: map[string]*Variable{expectedVars[0].Name: expectedVars[0]},
		Children:  []*ScopeNode{},
	}
	expectedTree.Children = append(expectedTree.Children, &ScopeNode{
		Level:     1,
		Parent:    expectedTree,
		Variables: map[string]*Variable{expectedVars[1].Name: expectedVars[1]},
		Children:  []*ScopeNode{},
	})
	expectedTree.Children = append(expectedTree.Children, &ScopeNode{
		Level:  0,
		Parent: expectedTree,
		Variables: map[string]*Variable{
			expectedVars[2].Name: expectedVars[2],
			expectedVars[3].Name: expectedVars[3],
		},
		Children: []*ScopeNode{},
	})
	expectedTree.Children[1].Children = append(expectedTree.Children[1].Children, &ScopeNode{
		Level:     1,
		Parent:    expectedTree.Children[1],
		Variables: map[string]*Variable{expectedVars[4].Name: expectedVars[4]},
		Children:  []*ScopeNode{},
	})
	expectedTree.Children[1].Children[0].Children = append(
		expectedTree.Children[1].Children[0].Children,
		&ScopeNode{
			Level:  2,
			Parent: expectedTree.Children[1].Children[0],
			Variables: map[string]*Variable{
				expectedVars[5].Name: expectedVars[5],
				expectedVars[6].Name: expectedVars[6],
			},
			Children: []*ScopeNode{},
		},
	)
	expectedTree.Children[1].Children = append(expectedTree.Children[1].Children, &ScopeNode{
		Level:     0,
		Parent:    expectedTree.Children[1],
		Variables: map[string]*Variable{expectedVars[7].Name: expectedVars[7]},
		Children:  []*ScopeNode{},
	})
	// Pass nil for VerilogFile as 'aa' contains only basic types for this test's scope,
	// and we are not testing user-defined type resolution here.
	// The `myPacket pkt0, pkt1;` line in `aa` will be skipped by MatchAllVariablesFromString
	// because `myPacket` is not a built-in type in the generalVariableRegex.
	parsedVars, scopeTree, err := ParseVariables(nil, aa)
	if err != nil {
		t.Fatalf("ParseVariables failed: %v", err)
	}

	if len(parsedVars) != len(expectedVars) {
		t.Fatalf("Expected %d variables, got %d variables.", len(expectedVars), len(parsedVars))
	}

	if !reflect.DeepEqual(parsedVars, expectedVars) {
			t.Errorf(
			"Parsed variables do not match expected variables.\nParsed: %+v\nExpected: %+v",
			parsedVars,
			expectedVars,
			)
		}

	// Compare scope trees
	if err := compareScopeTrees(scopeTree, expectedTree); err != nil {
		t.Errorf("Scope tree mismatch: %v", err)
		// For detailed visualization if the trees are small enough or for debugging:
		t.Logf("Actual Scope Tree: %+v", scopeTree)
		t.Logf("Expected Scope Tree: %+v", expectedTree)
	}
}

// compareScopeTrees recursively compares two ScopeNode trees.
// It returns an error if a mismatch is found.
func compareScopeTrees(actual, expected *ScopeNode) error {
	if actual == nil && expected == nil {
		return nil
	}
	if actual == nil || expected == nil {
		return fmt.Errorf(
			"one node is nil while the other is not (actual: %v, expected: %v)",
			actual != nil,
			expected != nil,
		)
	}

	if actual.Level != expected.Level {
		return fmt.Errorf("level mismatch: actual %d, expected %d", actual.Level, expected.Level)
	}

	if !reflect.DeepEqual(actual.Variables, expected.Variables) {
		var actualVarNames []string
		for _, v := range actual.Variables {
			if v != nil {
				actualVarNames = append(actualVarNames, v.Name)
			} else {
				actualVarNames = append(actualVarNames, "<nil>")
			}
		}
		var expectedVarNames []string
		for _, v := range expected.Variables {
			if v != nil {
				expectedVarNames = append(expectedVarNames, v.Name)
			} else {
				expectedVarNames = append(expectedVarNames, "<nil>")
			}
		}
		if !reflect.DeepEqual(expectedVarNames, actualVarNames) {
			return fmt.Errorf(
				"variables mismatch at level %d: actual names %v, expected names %v. Actual vars: %+v, Expected vars: %+v",
				actual.Level,
				actualVarNames,
				expectedVarNames,
				actual.Variables,
				expected.Variables,
			)
		}
	}

	if len(actual.Children) != len(expected.Children) {
		return fmt.Errorf(
			"children count mismatch at level %d: actual %d, expected %d",
			actual.Level,
			len(actual.Children),
			len(expected.Children),
		)
	}

	for i := range actual.Children {
		if err := compareScopeTrees(actual.Children[i], expected.Children[i]); err != nil {
			return fmt.Errorf("mismatch in child %d at level %d: %w", i, actual.Level, err)
		}
	}
	return nil
}

func TestParseVariables_MultipleDeclarations(t *testing.T) {
	testCases := []struct {
		name         string
		content      string
		expectedVars []*Variable
	}{
		{
			name: "Mixed single and multiple declarations",
			content: `
logic GGG_single1;
int GGG_multiA, GGG_multiB;
logic [3:0] GGG_nibble;
bit GGG_controlA, GGG_controlB, GGG_controlC;
`,
			expectedVars: []*Variable{
				{Name: "GGG_single1", Type: LOGIC, Width: 0, Unsigned: false},
				{Name: "GGG_multiA", Type: INT, Width: 0, Unsigned: false},
				{Name: "GGG_multiB", Type: INT, Width: 0, Unsigned: false},
				{Name: "GGG_nibble", Type: LOGIC, Width: 4, Unsigned: false},
				{Name: "GGG_controlA", Type: BIT, Width: 0, Unsigned: false},
				{Name: "GGG_controlB", Type: BIT, Width: 0, Unsigned: false},
				{Name: "GGG_controlC", Type: BIT, Width: 0, Unsigned: false},
			},
		},
		{
			name: "Multiple bit with rand and unsigned",
			content: `
rand bit unsigned GGG_flagX, GGG_flagY, GGG_flagZ;
`,
			expectedVars: []*Variable{
				{Name: "GGG_flagX", Type: BIT, Width: 0, Unsigned: true},
				{Name: "GGG_flagY", Type: BIT, Width: 0, Unsigned: true},
				{Name: "GGG_flagZ", Type: BIT, Width: 0, Unsigned: true},
			},
		},
		{
			name: "Multiple declarations with varied spacing",
			content: `
logic var_s1,var_s2;
int   var_s3 , var_s4 ;
logic [7:0] var_s5,  var_s6;
`,
			expectedVars: []*Variable{
				{Name: "var_s1", Type: LOGIC, Width: 0, Unsigned: false},
				{Name: "var_s2", Type: LOGIC, Width: 0, Unsigned: false},
				{Name: "var_s3", Type: INT, Width: 0, Unsigned: false},
				{Name: "var_s4", Type: INT, Width: 0, Unsigned: false},
				{Name: "var_s5", Type: LOGIC, Width: 8, Unsigned: false},
				{Name: "var_s6", Type: LOGIC, Width: 8, Unsigned: false},
			},
		},
		{
			name: "Multiple int with rand",
			content: `
rand int GGG_int1, GGG_int2;
`,
			expectedVars: []*Variable{
				{Name: "GGG_int1", Type: INT, Width: 0, Unsigned: false},
				{Name: "GGG_int2", Type: INT, Width: 0, Unsigned: false},
			},
		},
		{
			name: "Multiple logic with width",
			content: `
logic [15:0] GGG_busA, GGG_busB;
`,
			expectedVars: []*Variable{
				{Name: "GGG_busA", Type: LOGIC, Width: 16, Unsigned: false},
				{Name: "GGG_busB", Type: LOGIC, Width: 16, Unsigned: false},
			},
		},
		{
			name: "Multiple with array (array attribute not checked here)",
			content: `
logic [7:0] GGG_arrData1 [4], GGG_arrData2 [8];
int GGG_idx1, GGG_idx2 [10];
`,
			expectedVars: []*Variable{
				{
					Name:     "GGG_arrData1",
					Type:     LOGIC,
					Width:    8,
					Unsigned: false,
				}, // Array attribute not checked
				{
					Name:     "GGG_arrData2",
					Type:     LOGIC,
					Width:    8,
					Unsigned: false,
				}, // Array attribute not checked
				{Name: "GGG_idx1", Type: INT, Width: 0, Unsigned: false},
				{
					Name:     "GGG_idx2",
					Type:     INT,
					Width:    0,
					Unsigned: false,
				}, // Array attribute not checked
			},
		},
		{
			name: "Simple multiple logic",
			content: `
logic GGG_varA, GGG_varB, GGG_varC;
`,
			expectedVars: []*Variable{
				{Name: "GGG_varA", Type: LOGIC, Width: 0, Unsigned: false},
				{Name: "GGG_varB", Type: LOGIC, Width: 0, Unsigned: false},
				{Name: "GGG_varC", Type: LOGIC, Width: 0, Unsigned: false},
			},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			parsedVars, _, err := ParseVariables(nil, tc.content)
			if err != nil {
				t.Fatalf("ParseVariables failed for content '%s': %v", tc.content, err)
			}

			if len(parsedVars) != len(tc.expectedVars) {
				t.Fatalf(
					"Expected %d variables, got %d variables.\nContent:\n%s\nParsed: %+v\nExpected: %+v",
					len(tc.expectedVars),
					len(parsedVars),
					tc.content,
					parsedVars,
					tc.expectedVars,
				)
			}

			for _, expected := range tc.expectedVars {
				actual := parsedVars[expected.Name]
				if actual.Name != expected.Name ||
					actual.Type != expected.Type ||
					actual.Width != expected.Width ||
					actual.Unsigned != expected.Unsigned {
					t.Errorf(
						"Variable ('%s') mismatch:\nExpected: Name=%s, Type=%s (%d), Width=%d, Unsigned=%t\nActual:   Name=%s, Type=%s (%d), Width=%d, Unsigned=%t\nContent:\n%s",
						expected.Name,
						expected.Name,
						expected.Type.String(),
						expected.Type,
						expected.Width,
						expected.Unsigned,
						actual.Name,
						actual.Type.String(),
						actual.Type,
						actual.Width,
						actual.Unsigned,
						tc.content,
					)
				}
			}
		})
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
	vfile, err := ParseVerilog(dd, 5)
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
	$display("Hello, World!");
endmodule

module simple_sub(
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [8:0] sum
);
    // Simple adder logic
    assign sum = a - b;
endmodule

// top module
module top #(parameter GGGp = 8) (
    input logic [GGGp-1:0] GGGin,
    output logic [GGGp-1:0] GGGout
);

    logic [GGGp-1:0] GGGtemp_var = GGGin;

    always_comb begin
        //INJECT
        GGGout = GGGtemp_var;
    end

endmodule

`

func TestParseModules(t *testing.T) {
	// Test the regex for module
	vf := VerilogFile{
		Classes: make(map[string]*Class),
		Structs: make(map[string]*Struct),
	}
	ee = cleanText(ee)
	err := vf.ParseModules(ee)
	if err != nil {
		t.Fatalf("Failed to parse modules: %v", err)
	}
	modules := vf.Modules
	if len(modules) != 5 {
		t.Errorf("Ouin ouin not enough modules found, got %d, want 5", len(modules))
	}
}

var classss = `
class GGG_TopRandContainer #(parameter GGG_CONTAINER_WIDTH = 8);
    rand logic [GGG_CONTAINER_WIDTH-1:0] GGG_rand_var;
    // INJECT - Top container class body
endclass

class GGG_RandcContainer #(parameter GGG_CONTAINER_WIDTH = 4);
    randc logic [GGG_CONTAINER_WIDTH-1:0] GGG_randc_var;
    // INJECT - Randc container class body
endclass

class GGG_StructRandContainer;
    rand GGG_my_struct_t GGG_struct_var;
    // INJECT - Struct rand container class body
endclass

class GGG_ArrayRandContainer #(parameter GGG_CONTAINER_SIZE = 4);
    rand logic [7:0] GGG_array_var [GGG_CONTAINER_SIZE];
    // INJECT - Array rand container class body
endclass

`

func TestParseClasses(t *testing.T) {
	// Test the regex for class
	vf := VerilogFile{
		Classes: make(map[string]*Class),
		Structs: make(map[string]*Struct),
	}
	err := vf.ParseClasses(classss)
	if err != nil {
		t.Fatalf("Failed to parse classes: %v", err)
	}
	classes := vf.Classes
	if len(classes) != 4 {
		t.Errorf("Ouin ouin not enough classes found, got %d, want 4", len(classes))
	}
}

func TestDependancyGraph(t *testing.T) {
	rootDir, err := utils.GetRootDir()
	if err != nil {
		t.Fatalf("Failed to get root directory: %v", err)
	}
	snippetsDir := filepath.Join(rootDir, "snippets")
	filename := "task.sv"
	filename = filepath.Join(snippetsDir, filename)
	fileContent, err := utils.ReadFileContent(filename)
	if err != nil {
		t.Fatalf("Failed to read file content from %s", filename)
	}
	svFile, err := ParseVerilog(fileContent, 5)
	if err != nil {
		t.Fatalf("Failed to parse file content from %s", filename)
	}
	if svFile.DependancyMap == nil {
		t.Fatalf("Failed to parse dependancy map from %s", filename)
	}
}

func TestExtractANSIPortDeclarations(t *testing.T) {
	// Define common parameters for testing
	testParams := map[string]Parameter{
		"WIDTH":      {Name: "WIDTH", DefaultValue: "8"},
		"DATA_WIDTH": {Name: "DATA_WIDTH", DefaultValue: "32"},
		"ADDR_BUS":   {Name: "ADDR_BUS", DefaultValue: "16"},
	}

	testCases := []struct {
		name              string
		portListStr       string
		parameters        map[string]Parameter
		expectedPortsMap  map[string]Port
		expectedPortOrder []string
	}{
		{
			name:              "Empty port list",
			portListStr:       "",
			parameters:        nil,
			expectedPortsMap:  map[string]Port{},
			expectedPortOrder: []string{},
		},
		{
			name:        "Extra whitespace",
			portListStr: "  input   logic   [ 3 : 0 ]   spaced_out  , output wire normal_out",
			parameters:  nil,
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
				"addr": {Name: "addr", Direction: INOUT, Type: WIRE, Width: 16, IsSigned: true},
			},
			expectedPortOrder: []string{"addr"},
		},
		{
			name:        "Input logic with trailing comma",
			portListStr: "input logic clk,",
			parameters:  nil,
			expectedPortsMap: map[string]Port{
				"clk": {Name: "clk", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
			},
			expectedPortOrder: []string{"clk"},
		},
		{
			name:              "Malformed - missing name",
			portListStr:       "input logic [7:0]",
			parameters:        nil,
			expectedPortsMap:  map[string]Port{}, // Should not parse
			expectedPortOrder: []string{},
		},
		{
			name:        "Mixed ANSI and simple names",
			portListStr: "input logic start, stop, output [7:0] result",
			parameters:  nil,
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
				"clk": {Name: "clk", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
			},
			expectedPortOrder: []string{"clk"},
		},
		{
			name:              "Simple port names (non-ANSI in header style)",
			portListStr:       "clk, rst, data",
			parameters:        nil,
			expectedPortsMap:  map[string]Port{},
			expectedPortOrder: []string{},
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
	testParams := map[string]Parameter{
		"P_WIDTH":    {Name: "P_WIDTH", DefaultValue: "8"},
		"DATA_SIZE":  {Name: "DATA_SIZE", DefaultValue: "32"},
		"ADDR_LINES": {Name: "ADDR_LINES", DefaultValue: "16"},
	}

	testCases := []struct {
		name             string
		content          string
		parameters       map[string]Parameter
		expectedPortsMap map[string]Port
		expectError      bool
	}{
		{
			name: "Content with only comments",
			content: `// This is a comment
/* This is a
   multi-line comment */
wire clk; // Not a port declaration`,
			parameters:       nil,
			expectedPortsMap: map[string]Port{},
			expectError:      false,
		},
		{
			name:             "Empty content",
			content:          "",
			parameters:       nil,
			expectedPortsMap: map[string]Port{},
			expectError:      false,
		},
		{
			name: "Malformed port declaration - no name (should be skipped by parsePortDeclaration)",
			content: `
input logic [7:0];
output valid_out;
`,
			parameters: nil,
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
				"clk": {Name: "clk", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
			},
			expectError: false,
		},
		{
			name:       "Single output port with range",
			content:    "output reg [7:0] data_out;",
			parameters: nil,
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{
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

func TestParseParameters(t *testing.T) {
	testCases := []struct {
		name           string
		paramListStr   string
		expectedParams []Parameter
	}{
		{
			name:           "Empty parameter list",
			paramListStr:   "",
			expectedParams: []Parameter{},
		},
		{
			name:         "Extra whitespace",
			paramListStr: "  parameter   int    P_VAL   =  5  ,  NEXT_P  ",
			expectedParams: []Parameter{
				{Name: "P_VAL", Type: INT, DefaultValue: "5"},
				{Name: "NEXT_P", Type: INT, DefaultValue: ""},
			},
		},
		{
			name:         "Localparam (parsed as parameter)",
			paramListStr: "localparam STATE_IDLE = 0",
			expectedParams: []Parameter{
				{Name: "STATE_IDLE", Type: LOGIC, DefaultValue: "0", Localparam: true},
			},
		},
		{
			name:           "Malformed - just equals",
			paramListStr:   "= 5",
			expectedParams: []Parameter{},
		},
		{
			name:           "Malformed - missing name after type",
			paramListStr:   "parameter int = 5",
			expectedParams: []Parameter{},
		},
		{
			name:           "Malformed - parameter keyword alone",
			paramListStr:   "parameter",
			expectedParams: []Parameter{},
		},
		{
			name:           "Malformed - parameter with only type",
			paramListStr:   "parameter real",
			expectedParams: []Parameter{},
		},
		{
			name:         "Multiple parameters",
			paramListStr: "parameter A = 1, B = 2, C = 3",
			expectedParams: []Parameter{
				{Name: "A", Type: LOGIC, DefaultValue: "1"},
				{Name: "B", Type: INTEGER, DefaultValue: "2"},
				{Name: "C", Type: INTEGER, DefaultValue: "3"},
			},
		},
		{
			name:         "Multiple parameters with types",
			paramListStr: "parameter integer COUNT = 10, parameter real DELAY = 1.2, bit ENABLE = 1'b1",
			expectedParams: []Parameter{
				{Name: "COUNT", Type: INTEGER, DefaultValue: "10"},
				{Name: "DELAY", Type: REAL, DefaultValue: "1.2"},
				{Name: "ENABLE", Type: BIT, DefaultValue: "1'b1"},
			},
		},
		{
			name:         "Parameter with complex value including function call",
			paramListStr: `P_COMPLEX = $clog2(ANOTHER_PARAM + 1) - 1`,
			expectedParams: []Parameter{
				{Name: "P_COMPLEX", Type: UNKNOWN, DefaultValue: "$clog2(ANOTHER_PARAM + 1) - 1"},
			},
		},
		{
			name:         "Parameter with expression as default value",
			paramListStr: "ADDR_WIDTH = DATA_WIDTH / 2",
			expectedParams: []Parameter{
				{Name: "ADDR_WIDTH", Type: UNKNOWN, DefaultValue: "DATA_WIDTH / 2"},
			},
		},
		{
			name:         "Parameter with string default value",
			paramListStr: `FILENAME = "test.txt"`,
			expectedParams: []Parameter{
				{Name: "FILENAME", Type: STRING, DefaultValue: `"test.txt"`},
			},
		},
		{
			name:           "Parameter with trailing comma",
			paramListStr:   "P1 = 1,",
			expectedParams: []Parameter{{Name: "P1", Type: LOGIC, DefaultValue: "1"}},
		},
		{
			name:           "Parameter with type 'time'",
			paramListStr:   "parameter time SIM_TIME = 100ns",
			expectedParams: []Parameter{{Name: "SIM_TIME", Type: TIME, DefaultValue: "100ns"}},
		},
		{
			name:         "Parameter with type and signed-unsigned (type captures base)",
			paramListStr: "parameter integer unsigned MAX_COUNT = 100",
			expectedParams: []Parameter{
				{Name: "MAX_COUNT", Type: INTEGER, DefaultValue: "100"},
			}, // Regex captures 'integer' as type
		},
		{
			name:           "Single parameter no type no default",
			paramListStr:   "WIDTH",
			expectedParams: []Parameter{{Name: "WIDTH", Type: LOGIC, DefaultValue: ""}},
		},
		{
			name:           "Single parameter with default value",
			paramListStr:   "WIDTH = 8",
			expectedParams: []Parameter{{Name: "WIDTH", Type: INTEGER, DefaultValue: "8"}},
		},
		{
			name:           "Single parameter with type and default value",
			paramListStr:   "parameter int DATA_WIDTH = 32",
			expectedParams: []Parameter{{Name: "DATA_WIDTH", Type: INT, DefaultValue: "32"}},
		},
		{
			name:           "Single parameter with type no default",
			paramListStr:   "parameter logic CLK_PERIOD",
			expectedParams: []Parameter{{Name: "CLK_PERIOD", Type: LOGIC, DefaultValue: ""}},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			params, err := parseParameters(tc.paramListStr)
			if err != nil {
				t.Fatalf("parseParameters() error = %v", err)
			}

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
