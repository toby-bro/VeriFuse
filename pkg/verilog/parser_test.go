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

// Optional: Add tests specifically for parseRange if needed, though it's indirectly tested above.
func TestParseRange(t *testing.T) {
	// Add a test case for parameter resolution
	paramMap := map[string]*Parameter{
		"WIDTH": {Name: "WIDTH", DefaultValue: "16"},
		"ADDR":  {Name: "ADDR", DefaultValue: "32"},
	}

	testCases := []struct {
		name          string
		rangeStr      string
		params        map[string]*Parameter // Add params to test cases
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
			map[string]*Parameter{"NAME": {DefaultValue: "\"abc\""}},
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
				Ports: []*Port{
					{Name: "a", Direction: INPUT, Type: LOGIC, Width: 8, IsSigned: false},
					{Name: "b", Direction: INPUT, Type: LOGIC, Width: 8, IsSigned: false},
					{Name: "sum", Direction: OUTPUT, Type: LOGIC, Width: 9, IsSigned: false},
				},
				Body:       "\n    assign sum = a + b;\n",
				Parameters: []*Parameter{},
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
				Ports: []*Port{
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
				Parameters: []*Parameter{
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
		Level:  0,
		Parent: nil,
		Variables: map[string]*ScopeVariable{
			"GGG_field1": {Variable: expectedVars["GGG_field1"], Blocked: false},
		},
		Children: []*ScopeNode{},
	}
	expectedTree.Children = append(expectedTree.Children, &ScopeNode{
		Level:  1,
		Parent: expectedTree,
		Variables: map[string]*ScopeVariable{
			"GGG_field2": {Variable: expectedVars["GGG_field2"], Blocked: false},
		},
		Children: []*ScopeNode{},
	})
	expectedTree.Children = append(expectedTree.Children, &ScopeNode{
		Level:  0,
		Parent: expectedTree,
		Variables: map[string]*ScopeVariable{
			"GGG_condition_var": {Variable: expectedVars["GGG_condition_var"], Blocked: false},
			"GGG_array_var":     {Variable: expectedVars["GGG_array_var"], Blocked: false},
		},
		Children: []*ScopeNode{},
	})
	expectedTree.Children[1].Children = append(expectedTree.Children[1].Children, &ScopeNode{
		Level:  1,
		Parent: expectedTree.Children[1],
		Variables: map[string]*ScopeVariable{
			"GGG_index_limit": {Variable: expectedVars["GGG_index_limit"], Blocked: false},
		},
		Children: []*ScopeNode{},
	})
	expectedTree.Children[1].Children[0].Children = append(
		expectedTree.Children[1].Children[0].Children,
		&ScopeNode{
			Level:  2,
			Parent: expectedTree.Children[1].Children[0],
			Variables: map[string]*ScopeVariable{
				"m_queue": {Variable: expectedVars["m_queue"], Blocked: false},
				"GGG_class_rand_var": {
					Variable: expectedVars["GGG_class_rand_var"],
					Blocked:  false,
				},
			},
			Children: []*ScopeNode{},
		},
		&ScopeNode{
			Level:     1,
			Parent:    expectedTree.Children[1].Children[0],
			Variables: map[string]*ScopeVariable{},
			Children:  []*ScopeNode{},
		},
	)
	expectedTree.Children[1].Children = append(expectedTree.Children[1].Children, &ScopeNode{
		Level:  0,
		Parent: expectedTree.Children[1],
		Variables: map[string]*ScopeVariable{
			"internal_wire": {Variable: expectedVars["internal_wire"], Blocked: false},
		},
		Children: []*ScopeNode{},
	})
	// Pass nil for VerilogFile as 'aa' contains only basic types for this test's scope,
	// and we are not testing user-defined type resolution here.
	// The `myPacket pkt0, pkt1;` line in `aa` will be skipped by MatchAllVariablesFromString
	// because `myPacket` is not a built-in type in the generalVariableRegex.
	parsedVars, scopeTree, err := parseVariablesWithScope(nil, aa, nil, nil)
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
		t.Errorf(
			"Scope tree mismatch: %v, \nExpected: \n%s\nGot:\n%s",
			err,
			expectedTree.Dump(1),
			scopeTree.Dump(1),
		)
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
		for _, scopeVar := range actual.Variables {
			if scopeVar != nil && scopeVar.Variable != nil {
				actualVarNames = append(actualVarNames, scopeVar.Name)
			} else {
				actualVarNames = append(actualVarNames, "<nil>")
			}
		}
		var expectedVarNames []string
		for _, scopeVar := range expected.Variables {
			if scopeVar != nil && scopeVar.Variable != nil {
				expectedVarNames = append(expectedVarNames, scopeVar.Name)
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
			parsedVars, err := ParseVariables(nil, tc.content, nil)
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

module module_with_unpacked_array (
    input logic [1:0] array_index,
    output logic [3:0] array_out_val,
    input logic forced_input_driver,
    output logic forced_output_monitor,
    (* verilator public *) output logic [7:0] public_output_wire,
    input logic clk,
    input logic [3:0] array_in_val
);
    logic [3:0] unpacked_reg_array [0:3];
    (* verilator public *) logic [3:0] public_unpacked_array [0:1];
    (* wire_force_assign *) logic forced_internal_in;
    (* wire_force_release *) logic forced_internal_out;
    always_ff @(posedge clk) begin
        unpacked_reg_array[array_index] <= array_in_val;
        public_unpacked_array[0] <= array_in_val;
        public_unpacked_array[1] <= array_out_val;
    end
    assign array_out_val = unpacked_reg_array[array_index];
    assign public_output_wire = public_unpacked_array[0] + public_unpacked_array[1];
    logic local_clk_ref;
    assign local_clk_ref = clk;
    assign forced_internal_in = forced_input_driver;
    assign forced_output_monitor = forced_internal_out;
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
	if len(modules) != 7 {
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

func TestMatchClassInstantiationsFromString(t *testing.T) {
	// Create a mock VerilogFile with some classes for testing
	createMockVerilogFile := func(classNames []string) *VerilogFile {
		vf := &VerilogFile{
			Classes: make(map[string]*Class),
		}
		for _, name := range classNames {
			vf.Classes[name] = &Class{Name: name}
		}
		return vf
	}

	testCases := []struct {
		name          string
		classNames    []string
		content       string
		expectedFound []string
	}{
		{
			name:       "No classes defined",
			classNames: []string{},
			content: `
				module test;
					SomeClass obj = new();
				endmodule
			`,
			expectedFound: []string{},
		},
		{
			name:       "Direct instantiation with declaration",
			classNames: []string{"MyClass", "AnotherClass"},
			content: `
				module test;
					MyClass obj = new();
					AnotherClass obj2 = new(param1, param2);
				endmodule
			`,
			expectedFound: []string{"MyClass", "AnotherClass"},
		},
		{
			name:       "Variable declaration then assignment",
			classNames: []string{"TestClass", "UtilClass"},
			content: `
				module test;
					TestClass test_obj;
					UtilClass util_obj;
					
					initial begin
						test_obj = new();
						util_obj = new(arg1, arg2);
					end
				endmodule
			`,
			expectedFound: []string{"TestClass", "UtilClass"},
		},
		{
			name:       "Mixed direct and assignment patterns",
			classNames: []string{"DirectClass", "AssignClass"},
			content: `
				module test;
					DirectClass direct_obj = new();
					AssignClass assign_obj;
					
					initial begin
						assign_obj = new();
					end
				endmodule
			`,
			expectedFound: []string{"DirectClass", "AssignClass"},
		},
		{
			name:       "Multiple instantiations of same class",
			classNames: []string{"DuplicateClass"},
			content: `
				module test;
					DuplicateClass obj1 = new();
					DuplicateClass obj2;
					
					initial begin
						obj2 = new();
					end
				endmodule
			`,
			expectedFound: []string{"DuplicateClass"}, // Should only appear once
		},
		{
			name:       "Parameterized class instantiation",
			classNames: []string{"ParamClass"},
			content: `
				module test;
					ParamClass #(.WIDTH(8), .DEPTH(16)) param_obj = new();
				endmodule
			`,
			expectedFound: []string{"ParamClass"},
		},
		{
			name:       "Class instantiation with complex parameters",
			classNames: []string{"ComplexClass"},
			content: `
				module test;
					ComplexClass complex_obj = new(
						.param1(value1),
						.param2(value2),
						.param3(some_function(arg))
					);
				endmodule
			`,
			expectedFound: []string{"ComplexClass"},
		},
		{
			name:       "Array of class objects",
			classNames: []string{"ArrayClass"},
			content: `
				module test;
					ArrayClass array_obj[4];
					
					initial begin
						for (int i = 0; i < 4; i++) begin
							array_obj[i] = new();
						end
					end
				endmodule
			`,
			expectedFound: []string{"ArrayClass"},
		},
		{
			name:       "Class instantiation in function/task",
			classNames: []string{"FunctionClass", "TaskClass"},
			content: `
				module test;
					function void my_function();
						FunctionClass func_obj = new();
					endfunction
					
					task my_task();
						TaskClass task_obj;
						task_obj = new();
					endtask
				endmodule
			`,
			expectedFound: []string{"FunctionClass", "TaskClass"},
		},
		{
			name:       "Class instantiation with whitespace variations",
			classNames: []string{"SpaceClass"},
			content: `
				module test;
					SpaceClass   space_obj1   =   new(  );
					SpaceClass space_obj2;
					space_obj2   =   new(   );
				endmodule
			`,
			expectedFound: []string{"SpaceClass"},
		},
		{
			name:       "Class instantiation across multiple lines",
			classNames: []string{"MultilineClass"},
			content: `
				module test;
					MultilineClass multiline_obj = new(
						param1,
						param2,
						param3
					);
				endmodule
			`,
			expectedFound: []string{"MultilineClass"},
		},
		{
			name:       "No instantiations found",
			classNames: []string{"UnusedClass"},
			content: `
				module test;
					// No instantiations here
					logic signal;
				endmodule
			`,
			expectedFound: []string{},
		},
		{
			name:       "Class name as part of larger identifier (should not match)",
			classNames: []string{"Class"},
			content: `
				module test;
					MyClass obj = new(); // Should not match "Class"
					ClassHelper helper = new(); // Should not match "Class"  
				endmodule
			`,
			expectedFound: []string{},
		},
		{
			name:       "Class instantiation in generate block",
			classNames: []string{"GenClass"},
			content: `
				module test;
					generate
						for (genvar i = 0; i < 4; i++) begin
							GenClass gen_obj = new();
						end
					endgenerate
				endmodule
			`,
			expectedFound: []string{"GenClass"},
		},
		{
			name:       "Class instantiation in always block",
			classNames: []string{"AlwaysClass"},
			content: `
				module test;
					AlwaysClass always_obj;
					
					always_ff @(posedge clk) begin
						always_obj = new();
					end
				endmodule
			`,
			expectedFound: []string{"AlwaysClass"},
		},
		{
			name:       "Multiple classes with some unused",
			classNames: []string{"UsedClass1", "UsedClass2", "UnusedClass"},
			content: `
				module test;
					UsedClass1 obj1 = new();
					UsedClass2 obj2;
					obj2 = new();
					// UnusedClass is not instantiated
				endmodule
			`,
			expectedFound: []string{"UsedClass1", "UsedClass2"},
		},
		{
			name:       "Class instantiation with inheritance syntax",
			classNames: []string{"BaseClass", "DerivedClass"},
			content: `
				module test;
					BaseClass base_obj = new();
					DerivedClass derived_obj = new();
				endmodule
			`,
			expectedFound: []string{"BaseClass", "DerivedClass"},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			vf := createMockVerilogFile(tc.classNames)
			found := matchClassInstantiationsFromString(vf, tc.content)

			// Sort both slices to ensure consistent comparison
			sort.Strings(found)
			expectedSorted := make([]string, len(tc.expectedFound))
			copy(expectedSorted, tc.expectedFound)
			sort.Strings(expectedSorted)

			if !reflect.DeepEqual(found, expectedSorted) {
				t.Errorf(
					"matchClassInstantiationsFromString() = %v, want %v",
					found,
					expectedSorted,
				)
			}
		})
	}
}

func TestMatchClassInstantiationsFromStringEdgeCases(t *testing.T) {
	// Test edge cases and error conditions
	testCases := []struct {
		name          string
		classNames    []string
		content       string
		expectedFound []string
		description   string
	}{
		{
			name:          "Empty content",
			classNames:    []string{"TestClass"},
			content:       "",
			expectedFound: []string{},
			description:   "Should handle empty content gracefully",
		},
		{
			name:       "Commented out instantiations",
			classNames: []string{"CommentClass"},
			content: `
				module test;
					// CommentClass obj = new();
					/* CommentClass obj2 = new(); */
				endmodule
			`,
			expectedFound: []string{},
			description:   "Should not match commented out instantiations",
		},
		{
			name:       "String literals containing class names",
			classNames: []string{"StringClass"},
			content: `
				module test;
					string msg = "StringClass obj = new();";
				endmodule
			`,
			expectedFound: []string{},
			description:   "Should not match class names in string literals",
		},
		{
			name:       "Case sensitivity",
			classNames: []string{"CaseSensitive"},
			content: `
				module test;
					casesensitive obj = new(); // lowercase
					CASESENSITIVE obj2 = new(); // uppercase
				endmodule
			`,
			expectedFound: []string{},
			description:   "Should be case sensitive - no matches for different cases",
		},
		{
			name:       "Variable name same as class name",
			classNames: []string{"SameName"},
			content: `
				module test;
					SameName SameName = new();
				endmodule
			`,
			expectedFound: []string{"SameName"},
			description:   "Should handle case where variable name matches class name",
		},
		{
			name:       "Incomplete instantiation syntax",
			classNames: []string{"IncompleteClass"},
			content: `
				module test;
					IncompleteClass obj = new // Missing parentheses and semicolon
					IncompleteClass obj2 = new() // Missing semicolon
				endmodule
			`,
			expectedFound: []string{},
			description:   "Should not match incomplete instantiation syntax",
		},
		{
			name:       "Nested class instantiations",
			classNames: []string{"OuterClass", "InnerClass"},
			content: `
				module test;
					OuterClass outer_obj = new(InnerClass inner = new());
				endmodule
			`,
			expectedFound: []string{"OuterClass"},
			description:   "Should match outer class but might miss nested instantiations",
		},
		{
			name:       "Class instantiation with constructor arguments",
			classNames: []string{"ConstructorClass"},
			content: `
				module test;
					ConstructorClass obj = new(
						.width(8),
						.depth(16),
						.init_value('hFF)
					);
				endmodule
			`,
			expectedFound: []string{"ConstructorClass"},
			description:   "Should handle constructor with named arguments",
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			vf := &VerilogFile{
				Classes: make(map[string]*Class),
			}
			for _, name := range tc.classNames {
				vf.Classes[name] = &Class{Name: name}
			}

			found := matchClassInstantiationsFromString(vf, tc.content)

			// Sort both slices for consistent comparison
			sort.Strings(found)
			expectedSorted := make([]string, len(tc.expectedFound))
			copy(expectedSorted, tc.expectedFound)
			sort.Strings(expectedSorted)

			if !reflect.DeepEqual(found, expectedSorted) {
				t.Errorf("%s: matchClassInstantiationsFromString() = %v, want %v",
					tc.description, found, expectedSorted)
			}
		})
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
