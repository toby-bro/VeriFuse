package verilog

import (
	"testing"
)

func TestIsValidVariableName(t *testing.T) {
	tests := []struct {
		name     string
		varName  string
		expected bool
	}{
		{
			name:     "valid simple variable",
			varName:  "data",
			expected: true,
		},
		{
			name:     "valid variable with underscore",
			varName:  "data_out",
			expected: true,
		},
		{
			name:     "valid variable starting with underscore",
			varName:  "_internal_signal",
			expected: true,
		},
		{
			name:     "valid variable with numbers",
			varName:  "signal123",
			expected: true,
		},
		{
			name:     "empty string",
			varName:  "",
			expected: false,
		},
		{
			name:     "numeric literal",
			varName:  "123",
			expected: false,
		},
		{
			name:     "hex literal",
			varName:  "8'hFF",
			expected: false,
		},
		{
			name:     "binary literal",
			varName:  "4'b1010",
			expected: false,
		},
		{
			name:     "decimal literal",
			varName:  "32'd100",
			expected: false,
		},
		{
			name:     "expression with plus",
			varName:  "a+b",
			expected: false,
		},
		{
			name:     "expression with parentheses",
			varName:  "(signal)",
			expected: false,
		},
		{
			name:     "expression with brackets",
			varName:  "mem[0]",
			expected: false,
		},
		{
			name:     "constant zero",
			varName:  "1'b0",
			expected: false,
		},
		{
			name:     "constant one",
			varName:  "1'b1",
			expected: false,
		},
		{
			name:     "variable starting with number",
			varName:  "1signal",
			expected: false,
		},
		{
			name:     "variable with special characters",
			varName:  "signal$",
			expected: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := isValidVariableName(tt.varName)
			if result != tt.expected {
				t.Errorf(
					"isValidVariableName(%q) = %v, expected %v",
					tt.varName,
					result,
					tt.expected,
				)
			}
		})
	}
}

// createTestVerilogFileWithModules creates a VerilogFile with common test modules

// Helper function to get variable names from a map
func getVariableNames(variables map[string]*Variable) []string {
	names := make([]string, 0, len(variables))
	for name := range variables {
		names = append(names, name)
	}
	return names
}

// Helper function to find a variable in the scope tree and return its scope Variable and it's level
func findVariableInScopeTree(node *ScopeNode, varName string) (*Variable, int) {
	if node == nil {
		return nil, -1
	}

	// Check if variable is in current scope
	if sv, exists := node.Variables[varName]; exists {
		return sv, node.Level
	}

	// Recursively check children
	for _, child := range node.Children {
		if sv, level := findVariableInScopeTree(child, varName); level != -1 {
			return sv, level
		}
	}

	return nil, -1
}

func TestRemoveTaskClassScopeNodes(t *testing.T) {
	tests := []struct {
		name             string
		content          string
		expectedVarCount int
		expectedScopes   []string // Variables that should remain in scopes
		excludedScopes   []string // Variables that should be excluded from scopes
	}{
		{
			name: "task scope should be removed",
			content: `
				logic [7:0] global_var;
				
				task my_task;
					logic [7:0] task_var;
					logic internal_signal;
				endtask
				
				logic [7:0] another_global;
			`,
			expectedVarCount: 4, // All variables should be in variablesMap
			expectedScopes: []string{
				"global_var",
				"another_global",
			}, // Only these should be in scope tree
			excludedScopes: []string{
				"task_var",
				"internal_signal",
			}, // These should be excluded from scope tree
		},
		{
			name: "class scope should be removed",
			content: `
				logic [7:0] module_var;
				
				class MyClass;
					logic [7:0] class_var;
					integer count;
				endclass
				
				logic [7:0] final_var;
			`,
			expectedVarCount: 4, // All variables should be in variablesMap
			expectedScopes: []string{
				"module_var",
				"final_var",
			}, // Only these should be in scope tree
			excludedScopes: []string{
				"class_var",
				"count",
			}, // These should be excluded from scope tree
		},
		{
			name: "mixed task and class scopes should be removed",
			content: `
				logic [7:0] root_var;
				
				task test_task;
					logic [7:0] task_local;
				endtask
				
				logic [7:0] middle_var;
				
				class TestClass;
					logic [7:0] class_member;
					real value;
				endclass
				
				logic [7:0] end_var;
			`,
			expectedVarCount: 6, // All variables should be in variablesMap
			expectedScopes: []string{
				"root_var",
				"middle_var",
				"end_var",
			}, // Only these should be in scope tree
			excludedScopes: []string{
				"task_local",
				"class_member",
				"value",
			}, // These should be excluded from scope tree
		},
		{
			name: "nested task scope should be removed",
			content: `
				logic [7:0] outer_var;
				
				always_comb begin
					logic [7:0] always_var;
					
					task nested_task;
						logic [7:0] nested_task_var;
					endtask
				end
			`,
			expectedVarCount: 3, // All variables should be in variablesMap
			expectedScopes: []string{
				"outer_var",
				"always_var",
			}, // These should remain in scope tree
			excludedScopes: []string{
				"nested_task_var",
			}, // This should be excluded from scope tree
		},
		{
			name: "no task or class scopes",
			content: `
				logic [7:0] var1;
				
				always_comb begin
					logic [7:0] var2;
				end
				
				logic [7:0] var3;
			`,
			expectedVarCount: 3,                                // All variables should be in variablesMap
			expectedScopes:   []string{"var1", "var2", "var3"}, // All should remain in scope tree
			excludedScopes:   []string{},                       // None should be excluded
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			variables, scopeTree, err := parseVariablesWithScope(nil, tt.content, nil, nil, false)
			if err != nil {
				t.Fatalf("ParseVariables failed: %v", err)
			}

			// Check that all variables are in the variablesMap
			if len(variables) != tt.expectedVarCount {
				t.Errorf("Expected %d variables in variablesMap, got %d: %v",
					tt.expectedVarCount, len(variables), getVariableNames(variables))
			}

			// Check that expected variables are in the scope tree
			for _, varName := range tt.expectedScopes {
				if _, level := findVariableInScopeTree(scopeTree, varName); level == -1 {
					t.Errorf("Variable '%s' should be in scope tree but was not found", varName)
				}
			}

			// Check that excluded variables are NOT in the scope tree
			for _, varName := range tt.excludedScopes {
				if _, level := findVariableInScopeTree(scopeTree, varName); level != -1 {
					t.Errorf(
						"Variable '%s' should be excluded from scope tree but was found",
						varName,
					)
				}
			}

			// Verify that excluded variables are still in the variablesMap
			for _, varName := range tt.excludedScopes {
				if _, exists := variables[varName]; !exists {
					t.Errorf("Variable '%s' should be in variablesMap but was not found", varName)
				}
			}
		})
	}
}

func TestTaskClassScopeDetection(t *testing.T) {
	tests := []struct {
		name            string
		content         string
		expectedBlocked map[string]bool
	}{
		{
			name: "detect simple task scope",
			content: `
				task my_task;
					logic [7:0] task_var;
				endtask
			`,
			expectedBlocked: map[string]bool{
				"task_var": true,
			},
		},
		{
			name: "detect simple class scope",
			content: `
				class MyClass;
					logic [7:0] class_var;
				endclass
			`,
			expectedBlocked: map[string]bool{
				"class_var": true,
			},
		},
		{
			name: "detect multiple task/class scopes",
			content: `
				task task1;
					logic var1;
				endtask
				
				class Class1;
					logic var2;
				endclass
				
				task task2;
					logic var3;
				endtask
			`,
			expectedBlocked: map[string]bool{
				"var1": true,
				"var2": true,
				"var3": true,
			},
		},
		{
			name: "detect nested task in class",
			content: `
				class OuterClass;
					logic class_var;
					
					task inner_task;
						logic task_var;
					endtask
				endclass
			`,
			expectedBlocked: map[string]bool{
				"class_var": true,
				"task_var":  true,
			},
		},
		{
			name: "ignore non-task/class scopes",
			content: `
				always_comb begin
					logic always_var;
				end
				
				function int my_func;
					logic func_var;
				endfunction
			`,
			expectedBlocked: map[string]bool{
				"always_var": false,
				"func_var":   false,
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			taskClassVars := detectTaskClassScopeVariables(tt.content)

			for varName, shouldBeBlocked := range tt.expectedBlocked {
				isBlocked := taskClassVars[varName]
				if isBlocked != shouldBeBlocked {
					t.Errorf("Variable '%s' blocking status = %v, expected %v",
						varName, isBlocked, shouldBeBlocked)
				}
			}
		})
	}
}

func TestComplexTaskClassScopeRemoval(t *testing.T) {
	// Test a complex case with mixed scopes
	content := `
		logic [7:0] global1;
		
		always_comb begin
			logic [7:0] always_var;
			
			if (condition) begin
				logic [7:0] if_var;
			end
		end
		
		task complex_task;
			input logic [7:0] task_input;
			logic [7:0] task_local1;
			logic [7:0] task_local2;
			
			begin
				logic [7:0] task_block_var;
			end
		endtask
		
		logic [7:0] global2;
		
		class ComplexClass;
			logic [7:0] class_member1;
			
			function void class_func();
				logic [7:0] func_local;
			endfunction
			
			logic [7:0] class_member2;
		endclass
		
		logic [7:0] global3;
	`

	variables, scopeTree, err := parseVariablesWithScope(nil, content, nil, nil, false)
	if err != nil {
		t.Fatalf("ParseVariables failed: %v", err)
	}

	// All variables should be in variablesMap
	expectedTotalVars := 12 // Count all variables in the content
	if len(variables) != expectedTotalVars {
		t.Errorf("Expected %d variables in variablesMap, got %d: %v",
			expectedTotalVars, len(variables), getVariableNames(variables))
	}

	// Variables that should remain in scope tree (not in task/class)
	expectedInScope := []string{
		"global1", "global2", "global3",
		"always_var", "if_var",
	}

	// Variables that should be excluded from scope tree (in task/class)
	expectedExcluded := []string{
		"task_input", "task_local1", "task_local2", "task_block_var",
		"class_member1", "class_member2", "func_local",
	}

	// Check variables in scope tree
	for _, varName := range expectedInScope {
		if _, level := findVariableInScopeTree(scopeTree, varName); level == -1 {
			t.Errorf("Variable '%s' should be in scope tree but was not found", varName)
		}
	}

	// Check variables excluded from scope tree
	for _, varName := range expectedExcluded {
		if _, level := findVariableInScopeTree(scopeTree, varName); level != -1 {
			t.Errorf("Variable '%s' should be excluded from scope tree but was found", varName)
		}
	}

	// Verify all variables are still in variablesMap
	allExpectedVars := append(expectedInScope, expectedExcluded...) // nolint: gocritic
	for _, varName := range allExpectedVars {
		if _, exists := variables[varName]; !exists {
			t.Errorf("Variable '%s' should be in variablesMap but was not found", varName)
		}
	}

	t.Logf("Successfully processed complex mixed scopes")
	t.Logf("Variables in scope tree: %v", expectedInScope)
	t.Logf("Variables excluded from scope tree: %v", expectedExcluded)
}

func TestTaskClassScopeEdgeCases(t *testing.T) {
	tests := []struct {
		name             string
		content          string
		expectedInScope  []string
		expectedExcluded []string
	}{
		{
			name: "task keyword in comment should not affect parsing",
			content: `
				logic var1;
				// This is a comment about task functionality
				logic var2;
				/* Another comment mentioning class design */
				logic var3;
			`,
			expectedInScope:  []string{"var1", "var2", "var3"},
			expectedExcluded: []string{},
		},
		{
			name: "task and class at same indentation level",
			content: `
				logic global_var;
				
task task1;
	logic task_var1;
endtask

class Class1;
	logic class_var1;
endclass

				logic another_global;
			`,
			expectedInScope:  []string{"global_var", "another_global"},
			expectedExcluded: []string{"task_var1", "class_var1"},
		},
		{
			name: "empty task and class",
			content: `
				logic before_var;
				
				task empty_task;
				endtask
				
				class EmptyClass;
				endclass
				
				logic after_var;
			`,
			expectedInScope:  []string{"before_var", "after_var"},
			expectedExcluded: []string{},
		},
		{
			name: "task and class with only non-variable content",
			content: `
				logic setup_var;
				
				task display_task;
					$display("Hello World");
				endtask
				
				class UtilClass;
					parameter WIDTH = 8;
				endclass
				
				logic cleanup_var;
			`,
			expectedInScope:  []string{"setup_var", "cleanup_var"},
			expectedExcluded: []string{},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			variables, scopeTree, err := parseVariablesWithScope(nil, tt.content, nil, nil, false)
			if err != nil {
				t.Fatalf("ParseVariables failed: %v", err)
			}

			// Check variables in scope tree
			for _, varName := range tt.expectedInScope {
				if _, level := findVariableInScopeTree(scopeTree, varName); level == -1 {
					t.Errorf("Variable '%s' should be in scope tree but was not found", varName)
				}
			}

			// Check variables excluded from scope tree
			for _, varName := range tt.expectedExcluded {
				if _, level := findVariableInScopeTree(scopeTree, varName); level != -1 {
					t.Errorf(
						"Variable '%s' should be excluded from scope tree but was found",
						varName,
					)
				}
			}

			// Verify all variables are in variablesMap
			allExpectedVars := append( // nolint: gocritic
				tt.expectedInScope,
				tt.expectedExcluded...)
			for _, varName := range allExpectedVars {
				if _, exists := variables[varName]; !exists {
					t.Errorf("Variable '%s' should be in variablesMap but was not found", varName)
				}
			}
		})
	}
}

var nonAnsiScopeContent = `
/* Generated by Yosys 0.37+29 (git sha1 3c3788ee2, clang 10.0.0-4ubuntu1 -fPIC -Os) */

module topi(clkin_data, in_data, out_data);
    wire celloutsig_0_0z;
    wire [8:0] celloutsig_0_11z;
    reg [2:0] celloutsig_0_13z;
    wire celloutsig_0_14z;
    wire [6:0] celloutsig_0_17z;
    wire [14:0] celloutsig_0_1z;
    wire celloutsig_0_20z;
    wire celloutsig_0_21z;
    wire [7:0] celloutsig_0_24z;
    wire [3:0] celloutsig_0_2z;
    wire celloutsig_0_3z;
    wire celloutsig_0_4z;
    wire celloutsig_0_5z;
    wire [19:0] celloutsig_0_6z;
    wire celloutsig_0_7z;
    wire [12:0] celloutsig_0_8z;
    wire [12:0] celloutsig_0_9z;
    wire celloutsig_1_0z;
    wire celloutsig_1_10z;
    wire [10:0] celloutsig_1_11z;
    wire [2:0] celloutsig_1_12z;
    wire [20:0] celloutsig_1_13z;
    wire celloutsig_1_14z;
    wire [9:0] celloutsig_1_18z;
    wire celloutsig_1_19z;
    wire [4:0] celloutsig_1_1z;
    wire [3:0] celloutsig_1_2z;
    wire celloutsig_1_3z;
    wire celloutsig_1_4z;
    wire celloutsig_1_5z;
    wire [12:0] celloutsig_1_6z;
    wire celloutsig_1_7z;
    wire celloutsig_1_8z;
    wire [5:0] celloutsig_1_9z;
    input [63:0] clkin_data;
    wire [63:0] clkin_data;
    input [191:0] in_data;
    wire [191:0] in_data;
    output [191:0] out_data;
    wire [191:0] out_data;
    assign celloutsig_1_10z = ~(celloutsig_1_7z | celloutsig_1_4z);
    assign celloutsig_1_19z = ~(celloutsig_1_14z | celloutsig_1_9z[1]);
    assign celloutsig_0_5z = ~(in_data[15] | celloutsig_0_4z);
    assign celloutsig_1_0z = ~(in_data[118] | in_data[162]);
    assign celloutsig_0_3z = ~((celloutsig_0_0z | celloutsig_0_2z[3]) & (in_data[93] | celloutsig_0_0z));
    assign celloutsig_1_4z = ~((celloutsig_1_3z | celloutsig_1_0z) & (in_data[160] | celloutsig_1_3z));
    assign celloutsig_0_4z = celloutsig_0_3z | ~(celloutsig_0_3z);
    assign celloutsig_1_7z = celloutsig_1_6z[11] ^ celloutsig_1_6z[2];
    assign celloutsig_0_7z = celloutsig_0_1z[13] ^ in_data[79];
    assign celloutsig_0_21z = in_data[26] ^ celloutsig_0_9z[5];
    assign celloutsig_1_9z = { celloutsig_1_1z[3], celloutsig_1_4z, celloutsig_1_3z, celloutsig_1_3z, celloutsig_1_3z, celloutsig_1_5z } + celloutsig_1_6z[5:0];
    assign celloutsig_0_6z = { in_data[79], celloutsig_0_2z, celloutsig_0_1z } + { celloutsig_0_1z[10:6], celloutsig_0_1z };
    reg [11:0] _12_;
    always_ff @(posedge clkin_data[32], negedge celloutsig_1_19z)
        if (!celloutsig_1_19z) _12_ <= 12'h000;
        else _12_ <= { celloutsig_0_1z[12:4], celloutsig_0_4z, celloutsig_0_20z, celloutsig_0_14z };
    assign out_data[43:32] = _12_;
    assign celloutsig_0_17z = { celloutsig_0_11z[5:2], celloutsig_0_13z } & celloutsig_0_1z[12:6];
    assign celloutsig_0_24z = { celloutsig_0_17z[5:1], celloutsig_0_21z, celloutsig_0_7z, celloutsig_0_0z } & celloutsig_0_11z[8:1];
    assign celloutsig_1_1z = in_data[190:186] & { in_data[146:143], celloutsig_1_0z };
    assign celloutsig_1_2z = in_data[180:177] & in_data[146:143];
    assign celloutsig_0_0z = in_data[84:81] && in_data[47:44];
    assign celloutsig_1_5z = { in_data[172:170], celloutsig_1_4z, celloutsig_1_0z } && { celloutsig_1_1z[4], celloutsig_1_4z, celloutsig_1_4z, celloutsig_1_3z, celloutsig_1_0z };
    assign celloutsig_0_14z = celloutsig_0_13z[1] & ~(celloutsig_0_9z[12]);
    assign celloutsig_1_3z = celloutsig_1_2z[2] & ~(celloutsig_1_1z[3]);
    assign celloutsig_1_11z = { celloutsig_1_6z[11:6], celloutsig_1_10z, celloutsig_1_2z } % { 1'h1, celloutsig_1_2z[1:0], celloutsig_1_2z, celloutsig_1_5z, celloutsig_1_5z, celloutsig_1_8z, celloutsig_1_5z };
    assign celloutsig_1_13z = { in_data[176:174], celloutsig_1_1z, celloutsig_1_9z, celloutsig_1_9z, celloutsig_1_7z } % { 1'h1, in_data[121:113], celloutsig_1_1z, celloutsig_1_12z, celloutsig_1_7z, celloutsig_1_0z, celloutsig_1_3z };
    assign celloutsig_0_2z = { in_data[90:88], celloutsig_0_0z } % { 1'h1, celloutsig_0_1z[9:7] };
    assign celloutsig_1_18z = { in_data[162:161], celloutsig_1_9z, celloutsig_1_3z, celloutsig_1_14z } | { celloutsig_1_13z[14:12], celloutsig_1_12z, celloutsig_1_12z, celloutsig_1_5z };
    assign celloutsig_0_1z = { in_data[10:0], celloutsig_0_0z, celloutsig_0_0z, celloutsig_0_0z, celloutsig_0_0z } | in_data[31:17];
    assign celloutsig_1_14z = | { celloutsig_1_11z[6], celloutsig_1_12z };
    assign celloutsig_0_8z = in_data[85:73] << celloutsig_0_1z[12:0];
    assign celloutsig_0_11z = in_data[10:2] << celloutsig_0_1z[13:5];
    assign celloutsig_1_6z = { celloutsig_1_1z[2:1], celloutsig_1_4z, celloutsig_1_3z, celloutsig_1_0z, celloutsig_1_4z, celloutsig_1_1z, celloutsig_1_3z, celloutsig_1_0z } <<< { in_data[165:154], celloutsig_1_4z };
    assign celloutsig_1_12z = { celloutsig_1_11z[4:3], celloutsig_1_3z } <<< in_data[125:123];
    assign celloutsig_0_9z = in_data[45:33] <<< { celloutsig_0_6z[16:7], celloutsig_0_0z, celloutsig_0_5z, celloutsig_0_4z };
    assign celloutsig_0_20z = ~((celloutsig_0_0z & celloutsig_0_1z[8]) | celloutsig_0_8z[5]);
    always_latch
        if (celloutsig_1_19z) celloutsig_0_13z = 3'h0;
        else if (!clkin_data[0]) celloutsig_0_13z = celloutsig_0_8z[2:0];
    assign celloutsig_1_8z = ~((celloutsig_1_7z & in_data[168]) | (celloutsig_1_3z & celloutsig_1_2z[3]));
    assign { out_data[137:128], out_data[96], out_data[7:0] } = { celloutsig_1_18z, celloutsig_1_19z, celloutsig_0_24z };
endmodule`

func TestNonAnsiScopeVariables(t *testing.T) {
	svFile, err := ParseVerilog(nonAnsiScopeContent, 5)
	if err != nil {
		t.Fatalf("Failed to parse file content")
	}
	if svFile.DependencyMap == nil {
		t.Fatalf("Failed to parse dependancy map")
	}
	var module *Module
	for _, m := range svFile.Modules {
		module = m
		break
	}
	sc, err := GetScopeTree(svFile, module.Body, nil, module.Ports)
	if err != nil {
		t.Fatalf("Failed to get scope tree: %v", err)
	}
	if sc == nil {
		t.Fatalf("Scope tree is nil")
	}

	// Check that all the ports are in the root scope tree once and only once
	portNamesInRoot := make(map[string]bool)
	for _, port := range module.Ports {
		_, ok := sc.Variables[port.Name]
		if !ok {
			if port.Direction == INPUT {
				t.Errorf("Input port %s not found in root scope tree variables", port.Name)
			} else {
				t.Logf("Output port %s not found in root scope tree variables", port.Name)
			}
			continue
		}
		if portNamesInRoot[port.Name] {
			t.Errorf("Port %s found more than once in root scope tree variables", port.Name)
		}
		portNamesInRoot[port.Name] = true
	}

	// Recursively check child scopes for ports
	var checkChildScopesForPorts func(*ScopeNode, []*Port)
	checkChildScopesForPorts = func(node *ScopeNode, ports []*Port) {
		for _, child := range node.Children {
			for _, port := range ports {
				if _, ok := child.Variables[port.Name]; ok {
					t.Errorf(
						"Port %s found unexpectedly in child scope at level %d",
						port.Name,
						child.Level,
					)
				}
			}
			checkChildScopesForPorts(child, ports)
		}
	}

	checkChildScopesForPorts(sc, module.Ports)
}
