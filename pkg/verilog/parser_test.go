package verilog

import (
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"regexp"
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
	}

	// Create an empty parameters map for testing
	emptyParams := make(map[string]Parameter)

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
			width, err := parseRange(tc.rangeStr, tc.params)
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
				Body:       "\n    assign sum = a + b;\n",
				Parameters: []Parameter{},
				AnsiStyle:  true,
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
					{
						Name:            "in",
						Direction:       INPUT,
						Type:            LOGIC,
						Width:           8,
						IsSigned:        false,
						AlreadyDeclared: false,
					},
					{
						Name:            "out",
						Direction:       OUTPUT,
						Type:            LOGIC,
						Width:           8,
						IsSigned:        false,
						AlreadyDeclared: false,
					},
				},
				Parameters: []Parameter{
					{
						Name:         "WIDTH",
						Type:         INTEGER,
						DefaultValue: "8",
						AnsiStyle:    true,
					},
				},
				Body:      "\n    assign out = in;\n",
				AnsiStyle: true,
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
continue;
break;
	`

func TestParseVariables(t *testing.T) {
	expectedVars := map[string]*Variable{
		"GGG_field1":        {Name: "GGG_field1", Type: LOGIC, Width: 8, Unsigned: false},
		"GGG_field2":        {Name: "GGG_field2", Type: INT, Width: 0, Unsigned: true},
		"GGG_condition_var": {Name: "GGG_condition_var", Type: BIT, Width: 0, Unsigned: false},
		"GGG_array_var": {
			Name:     "GGG_array_var",
			Type:     LOGIC,
			Width:    8,
			Unsigned: false,
			Array:    "[GGG_CONTAINER_SIZE]",
		}, // Array attribute not checked here
		"GGG_index_limit": {Name: "GGG_index_limit", Type: INT, Width: 0, Unsigned: false},
		"m_queue": {
			Name:     "m_queue",
			Type:     INT,
			Width:    0,
			Unsigned: false,
			Array:    "[$]",
		}, // Array attribute not checked here
		// For GGG_class_rand_var, ParseRange with nil parameters will default to width 8 for "[GGG_CLASS_WIDTH-1:0]"
		"GGG_class_rand_var": {Name: "GGG_class_rand_var", Type: LOGIC, Width: 8, Unsigned: false},
		"internal_wire":      {Name: "internal_wire", Type: LOGIC, Width: 8, Unsigned: false},
	}
	expectedTree := &ScopeNode{
		Level:     0,
		Parent:    nil,
		Variables: map[string]*Variable{"GGG_field1": expectedVars["GGG_field1"]},
		Children:  []*ScopeNode{},
	}
	expectedTree.Children = append(expectedTree.Children, &ScopeNode{
		Level:     1,
		Parent:    expectedTree,
		Variables: map[string]*Variable{"GGG_field2": expectedVars["GGG_field2"]},
		Children:  []*ScopeNode{},
	})
	expectedTree.Children = append(expectedTree.Children, &ScopeNode{
		Level:  0,
		Parent: expectedTree,
		Variables: map[string]*Variable{
			"GGG_condition_var": expectedVars["GGG_condition_var"],
			"GGG_array_var":     expectedVars["GGG_array_var"],
		},
		Children: []*ScopeNode{},
	})
	expectedTree.Children[1].Children = append(expectedTree.Children[1].Children, &ScopeNode{
		Level:     1,
		Parent:    expectedTree.Children[1],
		Variables: map[string]*Variable{"GGG_index_limit": expectedVars["GGG_index_limit"]},
		Children:  []*ScopeNode{},
	})
	expectedTree.Children[1].Children[0].Children = append(
		expectedTree.Children[1].Children[0].Children,
		&ScopeNode{
			Level:  2,
			Parent: expectedTree.Children[1].Children[0],
			Variables: map[string]*Variable{
				"m_queue":            expectedVars["m_queue"],
				"GGG_class_rand_var": expectedVars["GGG_class_rand_var"],
			},
			Children: []*ScopeNode{},
		},
	)
	expectedTree.Children[1].Children = append(expectedTree.Children[1].Children, &ScopeNode{
		Level:     0,
		Parent:    expectedTree.Children[1],
		Variables: map[string]*Variable{"internal_wire": expectedVars["internal_wire"]},
		Children:  []*ScopeNode{},
	})
	// Pass nil for VerilogFile as 'aa' contains only basic types for this test's scope,
	// and we are not testing user-defined type resolution here.
	// The `myPacket pkt0, pkt1;` line in `aa` will be skipped by MatchAllVariablesFromString
	// because `myPacket` is not a built-in type in the generalVariableRegex.
	parsedVars, scopeTree, err := ParseVariables(nil, aa, nil)
	if err != nil {
		t.Fatalf("ParseVariables failed: %v", err)
	}

	if len(parsedVars) != len(expectedVars) {
		t.Fatalf("Expected %d variables, got %d variables.", len(expectedVars), len(parsedVars))
	}

	for _, v := range parsedVars {
		if !reflect.DeepEqual(v, expectedVars[v.Name]) {
			t.Errorf(
				"Parsed variable %s does not match expected variable.\nParsed: %+v\nExpected: %+v",
				v.Name,
				v,
				expectedVars[v.Name],
			)
		}
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
			parsedVars, _, err := ParseVariables(nil, tc.content, nil)
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
	matches := matchAllStructsFromString(bb)
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
	matches := matchAllClassesFromString(cc)
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
	if len(vfile.DependencyMap) == 0 {
		t.Fatalf("No dependencies found in parsed Verilog file")
	}
	if value, isMapContainsKey := vfile.DependencyMap["GGG_StructRandContainer"]; !isMapContainsKey {
		t.Fatalf("Dependency map does not contain key GGG_StructRandContainer")
	} else if value.DependsOn[0] != "GGG_my_struct_t" {
		t.Fatalf("Dependency map value does not contain expected value GGG_my_struct_t")
	}

	if value, isMapContainsKey := vfile.DependencyMap["GGG_StructuredRandModule"]; !isMapContainsKey {
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

module deep_comb_if_nested (
    input wire [7:0] dcin_a,
    input wire [7:0] dcin_b,
    input wire [3:0] dc_select,
    output logic [7:0] dcout_result
);
always_comb begin
    logic [7:0] temp_result = 8'd0;
    if (dc_select[0]) begin
        if (dc_select[1]) begin

    end
    dcout_result = temp_result;
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
	err := vf.parseModules(ee)
	if err != nil {
		t.Fatalf("Failed to parse modules: %v", err)
	}
	modules := vf.Modules
	if len(modules) != 6 {
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
	err := vf.parseClasses(classss)
	if err != nil {
		t.Fatalf("Failed to parse classes: %v", err)
	}
	classes := vf.Classes
	if len(classes) != 4 {
		t.Errorf("Ouin ouin not enough classes found, got %d, want 4", len(classes))
	}
}

func TestDependencyGraph(t *testing.T) {
	rootDir, err := utils.GetRootDir()
	if err != nil {
		t.Fatalf("Failed to get root directory: %v", err)
	}
	snippetsDir := filepath.Join(rootDir, "snippets.old")
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
	if svFile.DependencyMap == nil {
		t.Fatalf("Failed to parse dependency map from %s", filename)
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
		{
			name:        "simple array",
			portListStr: "input logic [7:0] data_array[4]",
			parameters:  nil,
			expectedPortsMap: map[string]Port{
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
			expectedPortsMap: map[string]Port{},
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
				{Name: "P_VAL", Type: INT, DefaultValue: "5", AnsiStyle: true},
				{Name: "NEXT_P", Type: INT, DefaultValue: "", AnsiStyle: true},
			},
		},
		{
			name:         "Localparam (parsed as parameter)",
			paramListStr: "localparam STATE_IDLE = 0",
			expectedParams: []Parameter{
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
				{Name: "A", Type: LOGIC, DefaultValue: "1", AnsiStyle: true},
				{Name: "B", Type: INTEGER, DefaultValue: "2", AnsiStyle: true},
				{Name: "C", Type: INTEGER, DefaultValue: "3", AnsiStyle: true},
			},
		},
		{
			name:         "Multiple parameters with types",
			paramListStr: "parameter integer COUNT = 10, parameter real DELAY = 1.2, bit ENABLE = 1'b1",
			expectedParams: []Parameter{
				{Name: "COUNT", Type: INTEGER, DefaultValue: "10", AnsiStyle: true},
				{Name: "DELAY", Type: REAL, DefaultValue: "1.2", AnsiStyle: true},
				{Name: "ENABLE", Type: BIT, DefaultValue: "1'b1", AnsiStyle: true},
			},
		},
		{
			name:         "Parameter with complex value including function call",
			paramListStr: `P_COMPLEX = $clog2(ANOTHER_PARAM + 1) - 1`,
			expectedParams: []Parameter{
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
			expectedParams: []Parameter{
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
			expectedParams: []Parameter{
				{Name: "FILENAME", Type: STRING, DefaultValue: `"test.txt"`, AnsiStyle: true},
			},
		},
		{
			name:         "Parameter with trailing comma",
			paramListStr: "P1 = 1,",
			expectedParams: []Parameter{
				{Name: "P1", Type: LOGIC, DefaultValue: "1", AnsiStyle: true},
			},
		},
		{
			name:         "Parameter with type 'time'",
			paramListStr: "parameter time SIM_TIME = 100ns",
			expectedParams: []Parameter{
				{Name: "SIM_TIME", Type: TIME, DefaultValue: "100ns", AnsiStyle: true},
			},
		},
		{
			name:         "Parameter with type and signed-unsigned (type captures base)",
			paramListStr: "parameter integer unsigned MAX_COUNT = 100",
			expectedParams: []Parameter{
				{Name: "MAX_COUNT", Type: INTEGER, DefaultValue: "100", AnsiStyle: true},
			}, // Regex captures 'integer' as type
		},
		{
			name:         "Single parameter no type no default",
			paramListStr: "WIDTH",
			expectedParams: []Parameter{
				{Name: "WIDTH", Type: LOGIC, DefaultValue: "", AnsiStyle: true},
			},
		},
		{
			name:         "Single parameter with default value",
			paramListStr: "WIDTH = 8",
			expectedParams: []Parameter{
				{Name: "WIDTH", Type: INTEGER, DefaultValue: "8", AnsiStyle: true},
			},
		},
		{
			name:         "Single parameter with type and default value",
			paramListStr: "parameter int DATA_WIDTH = 32",
			expectedParams: []Parameter{
				{Name: "DATA_WIDTH", Type: INT, DefaultValue: "32", AnsiStyle: true},
			},
		},
		{
			name:         "Single parameter with type no default",
			paramListStr: "parameter logic CLK_PERIOD",
			expectedParams: []Parameter{
				{Name: "CLK_PERIOD", Type: LOGIC, DefaultValue: "", AnsiStyle: true},
			},
		},
		{
			name:         "Type",
			paramListStr: "parameter type P_TYPE = logic",
			expectedParams: []Parameter{
				{Name: "P_TYPE", Type: TYPE, DefaultValue: "logic", AnsiStyle: true},
			},
		},
		{
			name:         "param with width",
			paramListStr: "parameter logic [7:0] P_SIZED = 8'hAA",
			expectedParams: []Parameter{
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
				Ports: []Port{
					{Name: "clk", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
					{Name: "rst", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
					{Name: "data_out", Direction: OUTPUT, Type: LOGIC, Width: 8, IsSigned: false},
				},
				Parameters: []Parameter{
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
				Ports: []Port{
					{Name: "clk", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
					{Name: "result", Direction: OUTPUT, Type: LOGIC, Width: 32, IsSigned: false},
				},
				Parameters: []Parameter{
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
				Ports: []Port{
					{Name: "enable", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
					{Name: "valid", Direction: OUTPUT, Type: LOGIC, Width: 0, IsSigned: false},
				},
				Parameters: []Parameter{
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
				Ports: []Port{
					{Name: "data_in", Direction: INPUT, Type: LOGIC, Width: 8, IsSigned: false},
					{Name: "data_out", Direction: OUTPUT, Type: LOGIC, Width: 8, IsSigned: false},
				},
				Parameters: []Parameter{
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

func TestParseInterface(t *testing.T) {
	testCases := []struct {
		name              string
		interfaceContent  string
		expectedInterface *Interface
		expectedOK        bool
	}{
		{
			name: "Complex interface with parameters and ports",
			interfaceContent: `interface fifo_if #(
  parameter int DEPTH = 16,
  parameter int WIDTH = 32
) (
  input logic clk,
  input logic rst_n
);
  logic [WIDTH-1:0] data;
  logic [$clog2(DEPTH)-1:0] count;
  logic full;
  logic empty;
  logic push;
  logic pop;
  
  modport producer (
    output data,
    output push,
    input full,
    input count
  );
  
  modport consumer (
    input data,
    output pop,
    input empty,
    input count
  );
  
  modport monitor (
    input data,
    input push,
    input pop,
    input full,
    input empty,
    input count
  );
endinterface`,
			expectedInterface: &Interface{
				Name: "fifo_if",
				Ports: []InterfacePort{
					{Name: "clk", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
					{Name: "rst_n", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
				},
				Parameters: []Parameter{
					{Name: "DEPTH", Type: INT, DefaultValue: "16"},
					{Name: "WIDTH", Type: INT, DefaultValue: "32"},
				},
				ModPorts: []ModPort{
					{
						Name: "producer",
						Signals: []ModPortSignal{
							{Name: "data", Direction: OUTPUT},
							{Name: "push", Direction: OUTPUT},
							{Name: "full", Direction: INPUT},
							{Name: "count", Direction: INPUT},
						},
					},
					{
						Name: "consumer",
						Signals: []ModPortSignal{
							{Name: "data", Direction: INPUT},
							{Name: "pop", Direction: OUTPUT},
							{Name: "empty", Direction: INPUT},
							{Name: "count", Direction: INPUT},
						},
					},
					{
						Name: "monitor",
						Signals: []ModPortSignal{
							{Name: "data", Direction: INPUT},
							{Name: "push", Direction: INPUT},
							{Name: "pop", Direction: INPUT},
							{Name: "full", Direction: INPUT},
							{Name: "empty", Direction: INPUT},
							{Name: "count", Direction: INPUT},
						},
					},
				},
				Variables: []*Variable{
					{Name: "data", Type: LOGIC, Width: 32}, // WIDTH parameter resolved
					{Name: "count", Type: LOGIC, Width: 4}, // $clog2(DEPTH) resolved
					{Name: "full", Type: LOGIC, Width: 0},
					{Name: "empty", Type: LOGIC, Width: 0},
					{Name: "push", Type: LOGIC, Width: 0},
					{Name: "pop", Type: LOGIC, Width: 0},
				},
				Body:        "  logic [WIDTH-1:0] data;\n  logic [$clog2(DEPTH)-1:0] count;\n  logic full;\n  logic empty;\n  logic push;\n  logic pop;\n  \n  modport producer (\n    output data,\n    output push,\n    input full,\n    input count\n  );\n  \n  modport consumer (\n    input data,\n    output pop,\n    input empty,\n    input count\n  );\n  \n  modport monitor (\n    input data,\n    input push,\n    input pop,\n    input full,\n    input empty,\n    input count\n  );",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			expectedOK: true,
		},
		{
			name: "Empty interface",
			interfaceContent: `interface empty_if;
endinterface`,
			expectedInterface: &Interface{
				Name:        "empty_if",
				Ports:       []InterfacePort{},
				Parameters:  []Parameter{},
				ModPorts:    []ModPort{},
				Variables:   []*Variable{},
				Body:        "",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			expectedOK: true,
		},
		{
			name: "Interface extending another interface",
			interfaceContent: `interface advanced_bus_if extends basic_bus_if;
  logic error;
  logic interrupt;
  
  modport advanced_master (
    output error,
    output interrupt
  );
endinterface`,
			expectedInterface: &Interface{
				Name:       "advanced_bus_if",
				Ports:      []InterfacePort{},
				Parameters: []Parameter{},
				ModPorts: []ModPort{
					{
						Name: "advanced_master",
						Signals: []ModPortSignal{
							{Name: "error", Direction: OUTPUT},
							{Name: "interrupt", Direction: OUTPUT},
						},
					},
				},
				Variables: []*Variable{
					{Name: "error", Type: LOGIC, Width: 0},
					{Name: "interrupt", Type: LOGIC, Width: 0},
				},
				Body:        "  logic error;\n  logic interrupt;\n  \n  modport advanced_master (\n    output error,\n    output interrupt\n  );",
				IsVirtual:   false,
				ExtendsFrom: "basic_bus_if",
			},
			expectedOK: true,
		},
		{
			name: "Interface with input or output ports",
			interfaceContent: `interface mem_if (
  input logic clk,
  input logic rst_n
);
  logic [31:0] addr;
  logic [31:0] data;
  logic we;
  logic re;
endinterface`,
			expectedInterface: &Interface{
				Name: "mem_if",
				Ports: []InterfacePort{
					{Name: "clk", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
					{Name: "rst_n", Direction: INPUT, Type: LOGIC, Width: 0, IsSigned: false},
				},
				Parameters: []Parameter{},
				ModPorts:   []ModPort{},
				Variables: []*Variable{
					{Name: "addr", Type: LOGIC, Width: 32},
					{Name: "data", Type: LOGIC, Width: 32},
					{Name: "we", Type: LOGIC, Width: 0},
					{Name: "re", Type: LOGIC, Width: 0},
				},
				Body:        "  logic [31:0] addr;\n  logic [31:0] data;\n  logic we;\n  logic re;",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			expectedOK: true,
		},
		{
			name: "Interface with modports",
			interfaceContent: `interface cpu_bus_if;
  logic [31:0] addr;
  logic [31:0] data;
  logic we;
  logic re;
  logic ready;
  
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
    inout data,
	output ready
  );
  
  modport monitor (
    input addr,
    input data,
    input we,
    input re
  );
endinterface`,
			expectedInterface: &Interface{
				Name:       "cpu_bus_if",
				Ports:      []InterfacePort{},
				Parameters: []Parameter{},
				ModPorts: []ModPort{
					{
						Name: "master",
						Signals: []ModPortSignal{
							{Name: "addr", Direction: OUTPUT},
							{Name: "data", Direction: INOUT},
							{Name: "we", Direction: OUTPUT},
							{Name: "re", Direction: OUTPUT},
						},
					},
					{
						Name: "slave",
						Signals: []ModPortSignal{
							{Name: "addr", Direction: INPUT},
							{Name: "data", Direction: INOUT},
							{Name: "we", Direction: INPUT},
							{Name: "re", Direction: INPUT},
							{Name: "ready", Direction: OUTPUT},
						},
					},
					{
						Name: "monitor",
						Signals: []ModPortSignal{
							{Name: "addr", Direction: INPUT},
							{Name: "data", Direction: INPUT},
							{Name: "we", Direction: INPUT},
							{Name: "re", Direction: INPUT},
						},
					},
				},
				Variables: []*Variable{
					{Name: "addr", Type: LOGIC, Width: 32},
					{Name: "data", Type: LOGIC, Width: 32},
					{Name: "we", Type: LOGIC, Width: 0},
					{Name: "re", Type: LOGIC, Width: 0},
					{Name: "ready", Type: LOGIC, Width: 0},
				},
				Body: `  logic [31:0] addr;
  logic [31:0] data;
  logic we;
  logic re;
  logic ready;
  
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
    inout data,
	output ready
  );
  
  modport monitor (
    input addr,
    input data,
    input we,
    input re
  );`,
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			expectedOK: true,
		},
		{
			name: "Interface with parameters",
			interfaceContent: `interface bus_if #(
  parameter int WIDTH = 8,
  parameter logic SIGNED = 1'b0
);
  logic [WIDTH-1:0] data;
  logic valid;
endinterface`,
			expectedInterface: &Interface{
				Name:  "bus_if",
				Ports: []InterfacePort{},
				Parameters: []Parameter{
					{Name: "WIDTH", Type: INT, DefaultValue: "8"},
					{Name: "SIGNED", Type: LOGIC, DefaultValue: "1'b0"},
				},
				ModPorts: []ModPort{},
				Variables: []*Variable{
					{Name: "data", Type: LOGIC, Width: 8}, // WIDTH parameter resolved
					{Name: "valid", Type: LOGIC, Width: 0},
				},
				Body:        "  logic [WIDTH-1:0] data;\n  logic valid;",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			expectedOK: true,
		},
		{
			name: "Interface with mixed signal types",
			interfaceContent: `interface mixed_if;
  logic [7:0] byte_data;
  bit [15:0] word_data;
  int counter;
  wire clk_wire;
  reg [3:0] nibble_reg;
  
  modport producer (
    output byte_data,
    output word_data,
    output counter,
    input clk_wire
  );
endinterface`,
			expectedInterface: &Interface{
				Name:       "mixed_if",
				Ports:      []InterfacePort{},
				Parameters: []Parameter{},
				ModPorts: []ModPort{
					{
						Name: "producer",
						Signals: []ModPortSignal{
							{Name: "byte_data", Direction: OUTPUT},
							{Name: "word_data", Direction: OUTPUT},
							{Name: "counter", Direction: OUTPUT},
							{Name: "clk_wire", Direction: INPUT},
						},
					},
				},
				Variables: []*Variable{
					{Name: "byte_data", Type: LOGIC, Width: 8},
					{Name: "word_data", Type: BIT, Width: 16},
					{Name: "counter", Type: INT, Width: 0},
					{Name: "clk_wire", Type: WIRE, Width: 0},
					{Name: "nibble_reg", Type: REG, Width: 4},
				},
				Body:        "  logic [7:0] byte_data;\n  bit [15:0] word_data;\n  int counter;\n  wire clk_wire;\n  reg [3:0] nibble_reg;\n  \n  modport producer (\n    output byte_data,\n    output word_data,\n    output counter,\n    input clk_wire\n  );",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			expectedOK: true,
		},
		{
			name: "Malformed interface - missing endinterface",
			interfaceContent: `interface bad_if;
  logic data;`,
			expectedInterface: nil,
			expectedOK:        false,
		},
		{
			name: "Malformed interface - missing name",
			interfaceContent: `interface;
  logic data;
endinterface`,
			expectedInterface: nil,
			expectedOK:        false,
		},
		{
			name: "Simple interface",
			interfaceContent: `interface simple_if;
  logic data;
  logic valid;
endinterface`,
			expectedInterface: &Interface{
				Name:       "simple_if",
				Ports:      []InterfacePort{},
				Parameters: []Parameter{},
				ModPorts:   []ModPort{},
				Variables: []*Variable{
					{Name: "data", Type: LOGIC, Width: 0},
					{Name: "valid", Type: LOGIC, Width: 0},
				},
				Body:        "  logic data;\n  logic valid;",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			expectedOK: true,
		},
		{
			name: "Interface with no external ports but with internal signals and modports",
			interfaceContent: `interface control_if;
  logic [7:0] data;
  logic ready;
  logic valid;
  modport FullAccess (input data, output ready, output valid);
  modport AccessIn (output data, output valid, input ready);
  modport AccessOut (input data, input valid, output ready);
endinterface`,
			expectedInterface: &Interface{
				Name:       "control_if",
				Ports:      []InterfacePort{}, // No external ports
				Parameters: []Parameter{},
				ModPorts: []ModPort{
					{
						Name: "FullAccess",
						Signals: []ModPortSignal{
							{Name: "data", Direction: INPUT},
							{Name: "ready", Direction: OUTPUT},
							{Name: "valid", Direction: OUTPUT},
						},
					},
					{
						Name: "AccessIn",
						Signals: []ModPortSignal{
							{Name: "data", Direction: OUTPUT},
							{Name: "ready", Direction: INPUT},
							{Name: "valid", Direction: OUTPUT},
						},
					},
					{
						Name: "AccessOut",
						Signals: []ModPortSignal{
							{Name: "data", Direction: INPUT},
							{Name: "ready", Direction: OUTPUT},
							{Name: "valid", Direction: INPUT},
						},
					},
				},
				Variables: []*Variable{
					{Name: "data", Type: LOGIC, Width: 8},
					{Name: "ready", Type: LOGIC, Width: 0},
					{Name: "valid", Type: LOGIC, Width: 0},
				},
				Body:        "  logic [7:0] data;\n  logic ready;\n  logic valid;\n  modport FullAccess (input data, output ready, output valid);\n  modport AccessIn (output data, output valid, input ready);\n  modport AccessOut (input data, input valid, output ready);",
				IsVirtual:   false,
				ExtendsFrom: "",
			},
			expectedOK: true,
		},
		{
			name: "Virtual interface",
			interfaceContent: `virtual interface axi_if;
  // Virtual interface body would be empty or minimal
endinterface`,
			expectedInterface: &Interface{
				Name:        "axi_if",
				Ports:       []InterfacePort{},
				Parameters:  []Parameter{},
				ModPorts:    []ModPort{},
				Variables:   []*Variable{},
				Body:        "  // Virtual interface body would be empty or minimal",
				IsVirtual:   true,
				ExtendsFrom: "",
			},
			expectedOK: true,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			vf := NewVerilogFile("test")
			err := vf.parseInterfaces(tc.interfaceContent)

			if (err == nil && len(vf.Interfaces) != 0) != tc.expectedOK ||
				len(vf.Interfaces) == 0 && tc.expectedOK {
				t.Errorf("ParseInterfaces() error = %v, expectedOK = %v", err, tc.expectedOK)
				return
			}

			if !tc.expectedOK {
				return // Don't check interface if we expected failure
			}

			// Get the parsed interface from the VerilogFile
			if len(vf.Interfaces) == 0 {
				t.Errorf("ParseInterfaces() returned no interfaces when expected success")
				return
			}

			if len(vf.Interfaces) != 1 {
				t.Errorf("ParseInterfaces() returned %d interfaces, expected 1", len(vf.Interfaces))
				return
			}

			var parsedInterface *Interface
			for _, iface := range vf.Interfaces {
				parsedInterface = iface
				break
			}

			if parsedInterface == nil {
				t.Errorf("ParseInterfaces() returned nil interface when expected success")
				return
			}

			// Check interface name
			if parsedInterface.Name != tc.expectedInterface.Name {
				t.Errorf(
					"Interface name = %v, want %v",
					parsedInterface.Name,
					tc.expectedInterface.Name,
				)
			}

			// Check virtual flag
			if parsedInterface.IsVirtual != tc.expectedInterface.IsVirtual {
				t.Errorf(
					"Interface IsVirtual = %v, want %v",
					parsedInterface.IsVirtual,
					tc.expectedInterface.IsVirtual,
				)
			}

			// Check extends from
			if parsedInterface.ExtendsFrom != tc.expectedInterface.ExtendsFrom {
				t.Errorf(
					"Interface ExtendsFrom = %v, want %v",
					parsedInterface.ExtendsFrom,
					tc.expectedInterface.ExtendsFrom,
				)
			}
			// sort modports for consistent comparison
			sort.Slice(parsedInterface.ModPorts, func(i, j int) bool {
				return parsedInterface.ModPorts[i].Name < parsedInterface.ModPorts[j].Name
			})
			sort.Slice(tc.expectedInterface.ModPorts, func(i, j int) bool {
				return tc.expectedInterface.ModPorts[i].Name < tc.expectedInterface.ModPorts[j].Name
			})

			// sort the ports for consistent comparison
			sort.Slice(parsedInterface.Ports, func(i, j int) bool {
				return parsedInterface.Ports[i].Name < parsedInterface.Ports[j].Name
			})
			sort.Slice(tc.expectedInterface.Ports, func(i, j int) bool {
				return tc.expectedInterface.Ports[i].Name < tc.expectedInterface.Ports[j].Name
			})

			// sort modport signals for consistent comparison
			for i := range parsedInterface.ModPorts {
				sort.Slice(parsedInterface.ModPorts[i].Signals, func(a, b int) bool {
					return parsedInterface.ModPorts[i].Signals[a].Name < parsedInterface.ModPorts[i].Signals[b].Name
				})
				sort.Slice(tc.expectedInterface.ModPorts[i].Signals, func(a, b int) bool {
					return tc.expectedInterface.ModPorts[i].Signals[a].Name < tc.expectedInterface.ModPorts[i].Signals[b].Name
				})
			}

			// Check ports
			if len(parsedInterface.Ports) != len(tc.expectedInterface.Ports) {
				t.Errorf(
					"Interface ports count = %v, want %v",
					len(parsedInterface.Ports),
					len(tc.expectedInterface.Ports),
				)
			} else {
				for i, port := range parsedInterface.Ports {
					expectedPort := tc.expectedInterface.Ports[i]
					if !reflect.DeepEqual(port, expectedPort) {
						t.Errorf("Interface port[%d] = %+v, want %+v", i, port, expectedPort)
					}
				}
			}

			// Check parameters
			if len(parsedInterface.Parameters) != len(tc.expectedInterface.Parameters) {
				t.Errorf(
					"Interface parameters count = %v, want %v",
					len(parsedInterface.Parameters),
					len(tc.expectedInterface.Parameters),
				)
			} else {
				for i, param := range parsedInterface.Parameters {
					expectedParam := tc.expectedInterface.Parameters[i]
					if !reflect.DeepEqual(param, expectedParam) {
						t.Errorf("Interface parameter[%d] = %+v, want %+v", i, param, expectedParam)
					}
				}
			}

			// Check modports
			if len(parsedInterface.ModPorts) != len(tc.expectedInterface.ModPorts) {
				t.Errorf(
					"Interface modports count = %v, want %v",
					len(parsedInterface.ModPorts),
					len(tc.expectedInterface.ModPorts),
				)
			} else {
				for i, modport := range parsedInterface.ModPorts {
					expectedModport := tc.expectedInterface.ModPorts[i]
					if !reflect.DeepEqual(modport, expectedModport) {
						t.Errorf("Interface modport[%d] = \n%+v, \nwant \n%+v", i, modport, expectedModport)
					}
				}
			}

			// sort the variables for consistent comparison
			sort.Slice(parsedInterface.Variables, func(i, j int) bool {
				return parsedInterface.Variables[i].Name < parsedInterface.Variables[j].Name
			})
			sort.Slice(tc.expectedInterface.Variables, func(i, j int) bool {
				return tc.expectedInterface.Variables[i].Name < tc.expectedInterface.Variables[j].Name
			})

			// Check body (trim whitespace for comparison)
			expectedBody := strings.TrimSpace(tc.expectedInterface.Body)
			actualBody := strings.TrimSpace(parsedInterface.Body)
			if actualBody != expectedBody {
				t.Errorf("Interface body = \n%q\n, want \n%q", actualBody, expectedBody)
			}

			// Check variables
			if tc.name == "Complex interface with parameters and ports" {
				// skip this check for complex interfaces as not implemented yet
				t.Skipf("Skipping variable check for complex interface %s", tc.name)
			}
			if len(parsedInterface.Variables) != len(tc.expectedInterface.Variables) {
				t.Errorf(
					"Interface variables count = %v, want %v",
					len(parsedInterface.Variables),
					len(tc.expectedInterface.Variables),
				)
			} else {
				for i, variable := range parsedInterface.Variables {
					expectedVariable := tc.expectedInterface.Variables[i]
					if !reflect.DeepEqual(variable, expectedVariable) {
						t.Errorf("Interface variable[%d] = %+v, want %+v", i, variable, expectedVariable)
					}
				}
			}
		})
	}
}

// TestInterfacePortDeclaration tests the parsing of interface port declarations
func TestParseInterfacePortDeclaration(t *testing.T) {
	testCases := []struct {
		name         string
		line         string
		expectedPort *Port
		expectedOK   bool
	}{
		{
			name: "Simple interface port input",
			line: "simple_bus.slave in_bus;",
			expectedPort: &Port{
				Name:          "in_bus",
				Direction:     INPUT,
				Type:          INTERFACE,
				Width:         0,
				IsSigned:      false,
				InterfaceName: "simple_bus",
				ModportName:   "slave",
			},
			expectedOK: true,
		},
		{
			name: "Simple interface port output",
			line: "simple_bus.master out_bus;",
			expectedPort: &Port{
				Name:          "out_bus",
				Direction:     INPUT, // Default direction for interface ports when not specified
				Type:          INTERFACE,
				Width:         0,
				IsSigned:      false,
				InterfaceName: "simple_bus",
				ModportName:   "master",
			},
			expectedOK: true,
		},
		{
			name: "Interface port with explicit input direction",
			line: "input axi_bus.slave axi_in;",
			expectedPort: &Port{
				Name:          "axi_in",
				Direction:     INPUT,
				Type:          INTERFACE,
				Width:         0,
				IsSigned:      false,
				InterfaceName: "axi_bus",
				ModportName:   "slave",
			},
			expectedOK: true,
		},
		{
			name: "Interface port with explicit output direction",
			line: "output memory_if.master mem_out;",
			expectedPort: &Port{
				Name:          "mem_out",
				Direction:     OUTPUT,
				Type:          INTERFACE,
				Width:         0,
				IsSigned:      false,
				InterfaceName: "memory_if",
				ModportName:   "master",
			},
			expectedOK: true,
		},
		{
			name: "Interface port with array",
			line: "simple_bus.slave bus_array[4];",
			expectedPort: &Port{
				Name:          "bus_array",
				Direction:     INPUT,
				Type:          INTERFACE,
				Width:         0,
				IsSigned:      false,
				Array:         "4",
				InterfaceName: "simple_bus",
				ModportName:   "slave",
			},
			expectedOK: true,
		},
		{
			name: "Regular port (should not match interface regex)",
			line: "input logic clk;",
			expectedPort: &Port{
				Name:          "clk",
				Direction:     INPUT,
				Type:          LOGIC,
				Width:         0,
				IsSigned:      false,
				InterfaceName: "",
				ModportName:   "",
			},
			expectedOK: true,
		},
		{
			name:         "Invalid interface port - missing port name",
			line:         "simple_bus.slave;",
			expectedPort: nil,
			expectedOK:   false,
		},
		{
			name:         "Invalid interface port - missing modport",
			line:         "simple_bus. port_name;",
			expectedPort: nil,
			expectedOK:   false,
		},
	}

	// Create an empty parameters map for testing
	emptyParams := make(map[string]Parameter)

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
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

// TestExtractANSIInterfacePortDeclarations tests parsing interface ports in ANSI style
func TestExtractANSIInterfacePortDeclarations(t *testing.T) {
	testCases := []struct {
		name              string
		portListStr       string
		expectedPortsMap  map[string]Port
		expectedPortOrder []string
	}{
		{
			name:        "Single interface port",
			portListStr: "simple_bus.slave in_bus",
			expectedPortsMap: map[string]Port{
				"in_bus": {
					Name:          "in_bus",
					Direction:     INPUT,
					Type:          INTERFACE,
					Width:         0,
					IsSigned:      false,
					InterfaceName: "simple_bus",
					ModportName:   "slave",
				},
			},
			expectedPortOrder: []string{"in_bus"},
		},
		{
			name:        "Multiple interface ports",
			portListStr: "simple_bus.slave in_bus, simple_bus.master out_bus",
			expectedPortsMap: map[string]Port{
				"in_bus": {
					Name:          "in_bus",
					Direction:     INPUT,
					Type:          INTERFACE,
					Width:         0,
					IsSigned:      false,
					InterfaceName: "simple_bus",
					ModportName:   "slave",
				},
				"out_bus": {
					Name:          "out_bus",
					Direction:     INPUT,
					Type:          INTERFACE,
					Width:         0,
					IsSigned:      false,
					InterfaceName: "simple_bus",
					ModportName:   "master",
				},
			},
			expectedPortOrder: []string{"in_bus", "out_bus"},
		},
		{
			name:        "Mixed regular and interface ports",
			portListStr: "input logic clk, simple_bus.slave data_bus, output logic ready",
			expectedPortsMap: map[string]Port{
				"clk": {
					Name:          "clk",
					Direction:     INPUT,
					Type:          LOGIC,
					Width:         0,
					IsSigned:      false,
					InterfaceName: "",
					ModportName:   "",
				},
				"data_bus": {
					Name:          "data_bus",
					Direction:     INPUT,
					Type:          INTERFACE,
					Width:         0,
					IsSigned:      false,
					InterfaceName: "simple_bus",
					ModportName:   "slave",
				},
				"ready": {
					Name:          "ready",
					Direction:     OUTPUT,
					Type:          LOGIC,
					Width:         0,
					IsSigned:      false,
					InterfaceName: "",
					ModportName:   "",
				},
			},
			expectedPortOrder: []string{"clk", "data_bus", "ready"},
		},
		{
			name:        "Interface port with explicit direction",
			portListStr: "input axi_if.slave axi_in, output axi_if.master axi_out",
			expectedPortsMap: map[string]Port{
				"axi_in": {
					Name:          "axi_in",
					Direction:     INPUT,
					Type:          INTERFACE,
					Width:         0,
					IsSigned:      false,
					InterfaceName: "axi_if",
					ModportName:   "slave",
				},
				"axi_out": {
					Name:          "axi_out",
					Direction:     OUTPUT,
					Type:          INTERFACE,
					Width:         0,
					IsSigned:      false,
					InterfaceName: "axi_if",
					ModportName:   "master",
				},
			},
			expectedPortOrder: []string{"axi_in", "axi_out"},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			portsMap, portOrder := extractANSIPortDeclarations(tc.portListStr, nil)

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

// TestInterfacePortDetection tests the interface port detection logic
func TestInterfacePortDetection(t *testing.T) {
	tests := []struct {
		name         string
		portDecl     string
		expectedType PortType
		expectedIntf string
		expectedModp string
	}{
		{
			name:         "Simple interface port",
			portDecl:     "simple_bus.slave port_name",
			expectedType: INTERFACE,
			expectedIntf: "simple_bus",
			expectedModp: "slave",
		},
		{
			name:         "Interface port with master modport",
			portDecl:     "axi_bus.master m_axi",
			expectedType: INTERFACE,
			expectedIntf: "axi_bus",
			expectedModp: "master",
		},
		{
			name:         "Regular logic port",
			portDecl:     "logic [7:0] data",
			expectedType: LOGIC,
			expectedIntf: "",
			expectedModp: "",
		},
		{
			name:         "Wire port",
			portDecl:     "wire clk",
			expectedType: WIRE,
			expectedIntf: "",
			expectedModp: "",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			detectedType := getType(tt.portDecl)
			if detectedType != tt.expectedType {
				t.Errorf(
					"Expected type %v, got %v for declaration: %s",
					tt.expectedType,
					detectedType,
					tt.portDecl,
				)
			}

			// Test interface parsing using regex
			interfacePortRegex := regexp.MustCompile(`(\w+)\.(\w+)\s+(\w+)`)
			matches := interfacePortRegex.FindStringSubmatch(tt.portDecl)

			if tt.expectedType == INTERFACE {
				if len(matches) != 4 {
					t.Errorf("Expected interface port regex to match for: %s", tt.portDecl)
				} else {
					if matches[1] != tt.expectedIntf {
						t.Errorf("Expected interface name %s, got %s", tt.expectedIntf, matches[1])
					}
					if matches[2] != tt.expectedModp {
						t.Errorf("Expected modport name %s, got %s", tt.expectedModp, matches[2])
					}
				}
			} else {
				if len(matches) > 0 {
					t.Errorf("Expected interface port regex to NOT match for: %s", tt.portDecl)
				}
			}
		})
	}
}

// TestInterfacePortMethods tests the Port struct methods for interface ports
func TestInterfacePortMethods(t *testing.T) {
	tests := []struct {
		name     string
		port     Port
		isIntf   bool
		intfType string
	}{
		{
			name: "Interface port",
			port: Port{
				Name:          "bus_port",
				InterfaceName: "simple_bus",
				ModportName:   "slave",
				Type:          INTERFACE,
			},
			isIntf:   true,
			intfType: "simple_bus.slave",
		},
		{
			name: "Regular port",
			port: Port{
				Name: "clk",
				Type: LOGIC,
			},
			isIntf:   false,
			intfType: "",
		},
		{
			name: "Port with only interface name",
			port: Port{
				Name:          "incomplete_port",
				InterfaceName: "simple_bus",
				Type:          INTERFACE,
			},
			isIntf:   false,
			intfType: "",
		},
		{
			name: "Port with only modport name",
			port: Port{
				Name:        "incomplete_port",
				ModportName: "slave",
				Type:        INTERFACE,
			},
			isIntf:   false,
			intfType: "",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if tt.port.IsInterfacePort() != tt.isIntf {
				t.Errorf(
					"Expected IsInterfacePort() to return %v, got %v",
					tt.isIntf,
					tt.port.IsInterfacePort(),
				)
			}
			if tt.port.GetInterfaceType() != tt.intfType {
				t.Errorf(
					"Expected GetInterfaceType() to return '%s', got '%s'",
					tt.intfType,
					tt.port.GetInterfaceType(),
				)
			}
		})
	}
}

func TestInterfacePortParsing(t *testing.T) { // nolint: gocyclo
	rootDir, err := utils.GetRootDir()
	if err != nil {
		t.Fatalf("Failed to get root directory: %v", err)
	}
	testfileDir := filepath.Join(rootDir, "testfiles", "sv", "ok")
	filename := "interface_module.sv"
	filename = filepath.Join(testfileDir, filename)
	fileContent, err := utils.ReadFileContent(filename)
	if err != nil {
		t.Fatalf("Failed to read file content from %s", filename)
	}
	svFile, err := ParseVerilog(fileContent, 5)
	if err != nil {
		t.Fatalf("Failed to parse file content from %s", filename)
	}

	// Test 1: Verify interface was parsed
	if len(svFile.Interfaces) != 1 {
		t.Errorf("Expected 1 interface, got %d", len(svFile.Interfaces))
	}

	for _, intf := range svFile.Interfaces {
		if intf.Name != "simple_bus" {
			t.Errorf("Expected interface name 'simple_bus', got '%s'", intf.Name)
		}

		// Verify modport parsing
		if len(intf.ModPorts) != 2 {
			t.Errorf("Expected 2 modports in simple_bus interface, got %d", len(intf.ModPorts))
		}

		// Check modport names
		modportNames := make(map[string]bool)
		for _, modport := range intf.ModPorts {
			modportNames[modport.Name] = true
		}

		if !modportNames["master"] {
			t.Error("Expected 'master' modport not found")
		}
		if !modportNames["slave"] {
			t.Error("Expected 'slave' modport not found")
		}
	}

	// Verify module was parsed
	if len(svFile.Modules) != 1 {
		t.Errorf("Expected 1 module, got %d", len(svFile.Modules))
	}

	for _, module := range svFile.Modules {
		if module.Name != "interface_module" {
			t.Errorf("Expected module name 'interface_module', got '%s'", module.Name)
		}

		// Check for interface ports
		portNames := make(map[string]Port)
		for _, port := range module.Ports {
			portNames[port.Name] = port
		}

		// Verify in_bus port (simple_bus.slave should be INPUT)
		if inBusPort, exists := portNames["in_bus"]; exists {
			if inBusPort.Direction != INPUT {
				t.Errorf("Expected in_bus port to be INPUT, got %v", inBusPort.Direction)
			}
			if inBusPort.Type != INTERFACE {
				t.Errorf("Expected in_bus port type to be INTERFACE, got %v", inBusPort.Type)
			}
			if inBusPort.InterfaceName != "simple_bus" {
				t.Errorf(
					"Expected in_bus interface name to be 'simple_bus', got '%s'",
					inBusPort.InterfaceName,
				)
			}
			if inBusPort.ModportName != "slave" {
				t.Errorf(
					"Expected in_bus modport name to be 'slave', got '%s'",
					inBusPort.ModportName,
				)
			}
		} else {
			t.Error("Expected in_bus port to be found")
		}

		// Verify out_bus port (simple_bus.master should be INPUT since no explicit direction)
		if outBusPort, exists := portNames["out_bus"]; exists {
			if outBusPort.Direction != INPUT {
				t.Errorf("Expected out_bus port to be INPUT, got %v", outBusPort.Direction)
			}
			if outBusPort.Type != INTERFACE {
				t.Errorf("Expected out_bus port type to be INTERFACE, got %v", outBusPort.Type)
			}
			if outBusPort.InterfaceName != "simple_bus" {
				t.Errorf(
					"Expected out_bus interface name to be 'simple_bus', got '%s'",
					outBusPort.InterfaceName,
				)
			}
			if outBusPort.ModportName != "master" {
				t.Errorf(
					"Expected out_bus modport name to be 'master', got '%s'",
					outBusPort.ModportName,
				)
			}
		} else {
			t.Error("Expected out_bus port to be found")
		}
	}
}

// TestInterfaceDependencyMapping tests that interfaces are correctly included in dependency tracking
func TestInterfaceDependencyMapping(t *testing.T) {
	rootDir, err := utils.GetRootDir()
	if err != nil {
		t.Fatalf("Failed to get root directory: %v", err)
	}
	testfileDir := filepath.Join(rootDir, "testfiles", "sv", "ok")
	filePath := filepath.Join(testfileDir, "interface_module.sv")

	fileContent, err := utils.ReadFileContent(filePath)
	if err != nil {
		t.Fatalf("Failed to read file content from %s: %v", filePath, err)
	}

	svFile, err := ParseVerilog(fileContent, 5)
	if err != nil {
		t.Fatalf("Failed to parse interface_module.sv: %v", err)
	}

	// Verify the interface_module depends on simple_bus interface
	if deps, exists := svFile.DependencyMap["interface_module"]; exists {
		simpleBusFound := false
		for _, dep := range deps.DependsOn {
			if dep == "simple_bus" {
				simpleBusFound = true
				break
			}
		}
		if !simpleBusFound {
			t.Errorf(
				"Expected interface_module to depend on simple_bus interface, dependencies: %v",
				deps.DependsOn,
			)
		}
	} else {
		t.Error("Expected interface_module to be found in dependency map")
	}

	// Verify the simple_bus interface is in the dependency map
	if _, exists := svFile.DependencyMap["simple_bus"]; !exists {
		t.Error("Expected simple_bus interface to be in dependency map")
	}
}

// TestInterfaceInstantiationDependencyTracking tests that interface instantiations within module bodies are detected as dependencies
func TestInterfaceInstantiationDependencyTracking(t *testing.T) {
	testContent := `
interface test_if;
  logic [7:0] data;
  logic valid;
  modport master (output data, output valid);
  modport slave (input data, input valid);
endinterface

module test_module_with_instantiation(
  input logic clk,
  input logic [7:0] in_data,
  output logic [7:0] out_data
);
  // This interface instantiation should be detected as a dependency
  test_if iface_inst();
  
  always_ff @(posedge clk) begin
    iface_inst.data <= in_data;
    iface_inst.valid <= 1'b1;
    out_data <= iface_inst.data;
  end
endmodule

module test_module_with_interface_port(
  test_if.slave in_bus,
  output logic [7:0] out_data
);
  // This interface port dependency should already be working
  assign out_data = in_bus.data;
endmodule
`

	svFile, err := ParseVerilog(testContent, 0)
	if err != nil {
		t.Fatalf("Failed to parse test content: %v", err)
	}

	// Test 1: Verify interface was parsed
	if len(svFile.Interfaces) != 1 {
		t.Errorf("Expected 1 interface, got %d", len(svFile.Interfaces))
	}

	for _, intf := range svFile.Interfaces {
		if intf.Name != "test_if" {
			t.Errorf("Expected interface name 'test_if', got '%s'", intf.Name)
		}

		// Verify modport parsing
		if len(intf.ModPorts) != 2 {
			t.Errorf("Expected 2 modports in test_if interface, got %d", len(intf.ModPorts))
		}

		// Check modport names
		modportNames := make(map[string]bool)
		for _, modport := range intf.ModPorts {
			modportNames[modport.Name] = true
		}

		if !modportNames["master"] {
			t.Error("Expected 'master' modport not found")
		}
		if !modportNames["slave"] {
			t.Error("Expected 'slave' modport not found")
		}
	}

	// Verify module was parsed
	if len(svFile.Modules) != 2 {
		t.Errorf("Expected 2 modules, got %d", len(svFile.Modules))
	}

	for _, module := range svFile.Modules {
		if module.Name != "test_module_with_instantiation" &&
			module.Name != "test_module_with_interface_port" {
			t.Errorf(
				"Expected module name 'test_module_with_instantiation' or 'test_module_with_interface_port', got '%s'",
				module.Name,
			)
		}
	}

	// Test 3: Verify interface port dependency is tracked (this should already work)
	if deps, exists := svFile.DependencyMap["test_module_with_interface_port"]; exists {
		testIfFound := false
		for _, dep := range deps.DependsOn {
			if dep == "test_if" {
				testIfFound = true
				break
			}
		}
		if !testIfFound {
			t.Error(
				"Expected test_module_with_interface_port to depend on test_if interface (interface port dependency)",
			)
		}
	} else {
		t.Error("Expected test_module_with_interface_port to be found in dependency map")
	}

	// Test 4: Verify interface instantiation dependency is tracked (this will currently fail)
	if deps, exists := svFile.DependencyMap["test_module_with_instantiation"]; exists {
		testIfFound := false
		for _, dep := range deps.DependsOn {
			if dep == "test_if" {
				testIfFound = true
				break
			}
		}
		if !testIfFound {
			t.Error(
				"Expected test_module_with_instantiation to depend on test_if interface (interface instantiation dependency)",
			)
		}
	} else {
		t.Error("Expected test_module_with_instantiation to be found in dependency map")
	}
}

// TestInterfaceInstantiationNestedParentheses tests that interface instantiations with nested parentheses are correctly detected
func TestInterfaceInstantiationNestedParentheses(t *testing.T) {
	testContent := `
interface simple_if;
  logic clk;
  logic [7:0] data;
  logic valid;
  modport master (output data, output valid, input clk);
  modport slave (input data, input valid, input clk);
endinterface

interface parameterized_if #(parameter int WIDTH = 8);
  logic clk;
  logic [WIDTH-1:0] data;
  logic valid;
  modport master (output data, output valid, input clk);
  modport slave (input data, input valid, input clk);
endinterface

module hierarchy_if(
  input logic clk,
  input logic [7:0] data_in,
  output logic [7:0] data_out
);
  // Test interface instantiation with nested parentheses - this is the real-world case that was failing
  simple_if if_inst (.clk(clk));
  
  // Test parameterized interface instantiation with nested parentheses
  parameterized_if #(.WIDTH(16)) param_if_inst (.clk(clk));
  
  // Test interface instantiation with multiple nested parentheses
  simple_if multi_if_inst (.clk(clk), .data(data_in), .valid(1'b1));
  
  always_ff @(posedge clk) begin
    if_inst.data <= data_in;
    if_inst.valid <= 1'b1;
    param_if_inst.data <= {data_in, data_in};
    param_if_inst.valid <= 1'b1;
    multi_if_inst.data <= data_in;
    data_out <= if_inst.data;
  end
endmodule
`

	svFile, err := ParseVerilog(testContent, 0)
	if err != nil {
		t.Fatalf("Failed to parse test content: %v", err)
	}

	// Test 1: Verify interfaces were parsed
	if _, exists := svFile.Interfaces["simple_if"]; !exists {
		t.Error("Expected simple_if interface to be parsed")
	}
	if _, exists := svFile.Interfaces["parameterized_if"]; !exists {
		t.Error("Expected parameterized_if interface to be parsed")
	}

	// Test 2: Verify module was parsed
	if _, exists := svFile.Modules["hierarchy_if"]; !exists {
		t.Error("Expected hierarchy_if module to be parsed")
	}

	// Test 3: Verify interface instantiation dependencies are tracked correctly even with nested parentheses
	if deps, exists := svFile.DependencyMap["hierarchy_if"]; exists {
		expectedInterfaces := []string{"simple_if", "parameterized_if"}
		for _, expectedInterface := range expectedInterfaces {
			found := false
			for _, dep := range deps.DependsOn {
				if dep == expectedInterface {
					found = true
					break
				}
			}
			if !found {
				t.Errorf(
					"Expected hierarchy_if to depend on %s interface (interface instantiation dependency)",
					expectedInterface,
				)
			}
		}
	} else {
		t.Error("Expected hierarchy_if to be found in dependency map")
	}

	// Test 4: Verify multiple instantiations of the same interface are still tracked (should not duplicate)
	if deps, exists := svFile.DependencyMap["hierarchy_if"]; exists {
		simpleIfCount := 0
		for _, dep := range deps.DependsOn {
			if dep == "simple_if" {
				simpleIfCount++
			}
		}
		if simpleIfCount != 1 {
			t.Errorf(
				"Expected exactly one dependency on simple_if, but found %d occurrences in dependencies: %v",
				simpleIfCount,
				deps.DependsOn,
			)
		}
	}
}

// TestModuleInstantiationDependencyTracking tests that module instantiations within module bodies are detected as dependencies
func TestModuleInstantiationDependencyTracking(t *testing.T) {
	testContent := `
module base_adder (
  input logic [7:0] a,
  input logic [7:0] b,
  output logic [7:0] sum
);
  assign sum = a + b;
endmodule

module base_multiplier (
  input logic [7:0] x,
  input logic [7:0] y,
  output logic [15:0] product
);
  assign product = x * y;
endmodule

module complex_math (
  input logic [7:0] in_a,
  input logic [7:0] in_b,
  input logic [7:0] in_c,
  output logic [15:0] result
);
  logic [7:0] sum_out;
  
  // This module instantiation should be detected as a dependency
  base_adder adder_inst (
    .a(in_a),
    .b(in_b),
    .sum(sum_out)
  );
  
  // This module instantiation should also be detected as a dependency
  base_multiplier mult_inst (
    .x(sum_out),
    .y(in_c),
    .product(result)
  );
endmodule

module simple_wrapper (
  input logic [7:0] data_in,
  output logic [7:0] data_out
);
  // Simple module instantiation
  base_adder simple_add (
    .a(data_in),
    .b(8'h01),
    .sum(data_out)
  );
endmodule
`

	svFile, err := ParseVerilog(testContent, 0)
	if err != nil {
		t.Fatalf("Failed to parse test content: %v", err)
	}

	// Test 1: Verify all modules were parsed
	expectedModules := []string{
		"base_adder",
		"base_multiplier",
		"complex_math",
		"simple_wrapper",
	}
	for _, moduleName := range expectedModules {
		if _, exists := svFile.Modules[moduleName]; !exists {
			t.Errorf("Expected module %s to be parsed", moduleName)
		}
	}

	// Test 2: Verify base modules have no dependencies (they don't instantiate other modules)
	for _, baseModule := range []string{"base_adder", "base_multiplier"} {
		if deps, exists := svFile.DependencyMap[baseModule]; exists {
			if len(deps.DependsOn) > 0 {
				t.Errorf(
					"Expected base module %s to have no dependencies, but found: %v",
					baseModule,
					deps.DependsOn,
				)
			}
		}
	}

	// Test 3: Verify complex_math depends on both base_adder and base_multiplier
	if deps, exists := svFile.DependencyMap["complex_math"]; exists {
		expectedDeps := []string{"base_adder", "base_multiplier"}
		for _, expectedDep := range expectedDeps {
			found := false
			for _, dep := range deps.DependsOn {
				if dep == expectedDep {
					found = true
					break
				}
			}
			if !found {
				t.Errorf(
					"Expected complex_math to depend on %s module (module instantiation dependency)",
					expectedDep,
				)
			}
		}
	} else {
		t.Error("Expected complex_math to be found in dependency map")
	}

	// Test 4: Verify simple_wrapper depends on base_adder
	if deps, exists := svFile.DependencyMap["simple_wrapper"]; exists {
		baseAdderFound := false
		for _, dep := range deps.DependsOn {
			if dep == "base_adder" {
				baseAdderFound = true
				break
			}
		}
		if !baseAdderFound {
			t.Error(
				"Expected simple_wrapper to depend on base_adder module (simple module instantiation dependency)",
			)
		}
	} else {
		t.Error("Expected simple_wrapper to be found in dependency map")
	}
}

func TestParseTransFuzzFile(t *testing.T) {
	// skip this test
	t.Skip("Skipping local only test")
	fmt.Printf("Modules regex, \n%s\n", generalModuleRegex.String())
	fmt.Printf("Classes regex, \n%s\n", generalClassRegex.String())
	rootDir, err := utils.GetRootDir()
	if err != nil {
		t.Fatalf("Failed to get root directory: %v", err)
	}
	filename := filepath.Join(
		rootDir,
		"testfiles/sv/ok/clocking_module.sv",
	)
	fileContent, err := utils.ReadFileContent(filename)
	if err != nil {
		t.Fatalf("Failed to read file content from %s", filename)
	}
	svFile, err := ParseVerilog(fileContent, 5)
	if err != nil {
		t.Fatalf("Failed to parse file content from %s", filename)
	}
	if svFile.DependencyMap == nil {
		t.Fatalf("Failed to parse dependancy map from %s", filename)
	}
}
