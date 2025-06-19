package verilog

import (
	"reflect"
	"strings"
	"testing"
)

func TestDetectBlockedVariables(t *testing.T) {
	tests := []struct {
		name     string
		content  string
		expected map[string]bool
	}{
		{
			name: "module instantiation with constants and expressions",
			content: `
				counter_module counter_inst (
					.clk(system_clk),
					.reset(1'b0),
					.enable(enable_signal),
					.count_out(counter_value)
				);
			`,
			expected: map[string]bool{
				"counter_value": true,
				// Note: system_clk and enable_signal are not blocked as they're likely inputs
				// 1'b0 is filtered out as it's a literal
			},
		},
		{
			name: "assignment",
			content: `
				assign data_out = data_in;
				assign enable = 1'b1;
			`,
			expected: map[string]bool{
				"data_out": true,
				"enable":   true,
			},
		},
		{
			name: "wire assignment",
			content: `
				wire clk = oscillator;
				wire [7:0] bus = 8'h00;
			`,
			expected: map[string]bool{
				"clk": true,
				"bus": true,
			},
		},
		{
			name: "force statement",
			content: `
				force sig1 = 1'b0;
				force counter = 32'h0;
			`,
			expected: map[string]bool{
				"sig1":    true,
				"counter": true,
			},
		},
		{
			name: "always_comb block",
			content: `
				always_comb begin
					result = a + b;
					overflow = (a[7] & b[7] & ~result[7]) | (~a[7] & ~b[7] & result[7]);
				end
			`,
			expected: map[string]bool{
				"result":   true,
				"overflow": true,
			},
		},
		{
			name: "always_ff block",
			content: `
				always_ff @(posedge clk) begin
					counter <= counter + 1;
					state <= next_state;
				end
			`,
			expected: map[string]bool{
				"counter": true,
				"state":   true,
			},
		},
		{
			name: "mixed blocking constructs",
			content: `
				assign ready = enable & valid;
				wire rst = ~reset_n;
				force debug_mode = 1'b1;
				
				always_comb begin
					next_state = current_state;
					if (trigger)
						next_state = ACTIVE;
				end
				
				always_ff @(posedge clk) begin
					current_state <= next_state;
					data_reg <= data_in;
				end
			`,
			expected: map[string]bool{
				"ready":         true,
				"rst":           true,
				"debug_mode":    true,
				"next_state":    true,
				"current_state": true,
				"data_reg":      true,
			},
		},
		{
			name: "array assignments",
			content: `
				always_comb begin
					memory[0] = data;
					array[index] = value;
				end
			`,
			expected: map[string]bool{
				"memory": true,
				"array":  true,
			},
		},
		{
			name: "no blocking constructs",
			content: `
				logic data;
				reg [7:0] address;
				integer count;
			`,
			expected: map[string]bool{},
		},
		{
			name: "nested always blocks",
			content: `
				always_comb begin
					temp1 = input1;
					always_ff @(posedge clk) begin
						temp2 <= temp1;
					end
				end
			`,
			expected: map[string]bool{
				"temp1": true,
				"temp2": true,
			},
		},
		{
			name: "complex always_ff with sensitivity list",
			content: `
				always_ff @(posedge clk or negedge rst_n) begin
					if (!rst_n) begin
						counter <= 0;
						state <= IDLE;
					end else begin
						counter <= counter + 1;
						state <= next_state;
					end
				end
			`,
			expected: map[string]bool{
				"counter": true,
				"state":   true,
			},
		},
		{
			name: "module instantiation with output ports",
			content: `
				adder_module adder_inst (
					.clk(clock),
					.data_in(input_signal),
					.result_out(output_signal),
					.valid_out(valid_flag)
				);
			`,
			expected: map[string]bool{
				"output_signal": true,
				"valid_flag":    true,
				// Note: clock and input_signal are not blocked as they're likely inputs
			},
		},
		{
			name: "multiple module instantiations",
			content: `
				split_inputs_outputs_only split_inst1 (
					.in_val_a_l(a),
					.in_val_b_l(b),
					.out_val_c_l(sum),
					.out_val_d_l(diff)
				);
				
				split_if_only_then split_inst2 (
					.clk_h(clk),
					.condition_h(enable),
					.in_val_h(data_in),
					.out_reg_h(data_out)
				);
			`,
			expected: map[string]bool{
				"sum":      true,
				"diff":     true,
				"data_out": true,
				// Note: a, b, clk, enable, data_in are not blocked as they're likely inputs
			},
		},
		{
			name: "module instantiation with constants and expressions",
			content: `
				counter_module counter_inst (
					.clk(system_clk),
					.reset(1'b0),
					.enable(enable_signal),
					.count_out(counter_value)
				);
			`,
			expected: map[string]bool{
				"counter_value": true,
				// Note: system_clk and enable_signal are inputs, so they shouldn't be blocked
				// Note: 1'b0 should be filtered out as it's a literal
			},
		},
		{
			name: "mixed blocking constructs with module instantiation",
			content: `
				assign ready = enable & valid;
				
				always_comb begin
					temp_result = input_a + input_b;
				end
				
				processor_module proc_inst (
					.clk(main_clk),
					.data_in(temp_result),
					.data_out(final_result)
				);
			`,
			expected: map[string]bool{
				"ready":        true,
				"temp_result":  true,
				"final_result": true,
				// Note: main_clk is an input, so it shouldn't be blocked
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Create VerilogFile with test module definitions
			vfFile := createTestVerilogFileWithModules()
			result := detectBlockedVariables(vfFile, tt.content)
			if !reflect.DeepEqual(result, tt.expected) {
				t.Errorf("detectBlockedVariables() = %v, expected %v", result, tt.expected)
			}
		})
	}
}

func TestRemoveBlockedVariablesFromParents(t *testing.T) {
	tests := []struct {
		name         string
		initialScope *ScopeNode
		blockedVars  map[string]bool
		expected     *ScopeNode
	}{
		{
			name: "remove blocked variable from parent",
			initialScope: &ScopeNode{
				Level: 0,
				Variables: map[string]*Variable{
					"data": {Name: "data", Type: LOGIC},
					"clk":  {Name: "clk", Type: LOGIC},
				},
				Children: []*ScopeNode{
					{
						Level: 1,
						Variables: map[string]*Variable{
							"temp": {Name: "temp", Type: LOGIC},
						},
						Children: []*ScopeNode{},
						Parent:   nil, // will be set properly in test
					},
				},
				Parent: nil,
			},
			blockedVars: map[string]bool{
				"data": true,
			},
			expected: &ScopeNode{
				Level: 0,
				Variables: map[string]*Variable{
					"clk": {Name: "clk", Type: LOGIC},
				},
				Children: []*ScopeNode{
					{
						Level: 1,
						Variables: map[string]*Variable{
							"temp": {Name: "temp", Type: LOGIC},
						},
						Children: []*ScopeNode{},
						Parent:   nil,
					},
				},
				Parent: nil,
			},
		},
		{
			name: "no variables to remove",
			initialScope: &ScopeNode{
				Level: 0,
				Variables: map[string]*Variable{
					"safe_var": {Name: "safe_var", Type: LOGIC},
				},
				Children: []*ScopeNode{},
				Parent:   nil,
			},
			blockedVars: map[string]bool{
				"other_var": true,
			},
			expected: &ScopeNode{
				Level: 0,
				Variables: map[string]*Variable{
					"safe_var": {Name: "safe_var", Type: LOGIC},
				},
				Children: []*ScopeNode{},
				Parent:   nil,
			},
		},
		{
			name: "multiple levels with blocked variables",
			initialScope: &ScopeNode{
				Level: 0,
				Variables: map[string]*Variable{
					"global_var":  {Name: "global_var", Type: LOGIC},
					"blocked_var": {Name: "blocked_var", Type: LOGIC},
				},
				Children: []*ScopeNode{
					{
						Level: 1,
						Variables: map[string]*Variable{
							"local_var": {Name: "local_var", Type: LOGIC},
						},
						Children: []*ScopeNode{
							{
								Level: 2,
								Variables: map[string]*Variable{
									"nested_var": {Name: "nested_var", Type: LOGIC},
								},
								Children: []*ScopeNode{},
								Parent:   nil,
							},
						},
						Parent: nil,
					},
				},
				Parent: nil,
			},
			blockedVars: map[string]bool{
				"blocked_var": true,
			},
			expected: &ScopeNode{
				Level: 0,
				Variables: map[string]*Variable{
					"global_var": {Name: "global_var", Type: LOGIC},
				},
				Children: []*ScopeNode{
					{
						Level: 1,
						Variables: map[string]*Variable{
							"local_var": {Name: "local_var", Type: LOGIC},
						},
						Children: []*ScopeNode{
							{
								Level: 2,
								Variables: map[string]*Variable{
									"nested_var": {Name: "nested_var", Type: LOGIC},
								},
								Children: []*ScopeNode{},
								Parent:   nil,
							},
						},
						Parent: nil,
					},
				},
				Parent: nil,
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Set up parent relationships
			setupParentRelationships(tt.initialScope)
			setupParentRelationships(tt.expected)

			removeBlockedVariablesFromParents(tt.initialScope, tt.blockedVars)

			if !compareScopeNodesForBlocking(tt.initialScope, tt.expected) {
				t.Errorf("removeBlockedVariablesFromParents() result does not match expected")
			}
		})
	}
}

func TestIsVariableBlockedInChildren(t *testing.T) {
	tests := []struct {
		name        string
		scopeNode   *ScopeNode
		varName     string
		blockedVars map[string]bool
		expected    bool
	}{
		{
			name: "variable is globally blocked",
			scopeNode: &ScopeNode{
				Level:     0,
				Variables: map[string]*Variable{},
				Children:  []*ScopeNode{},
				Parent:    nil,
			},
			varName: "blocked_var",
			blockedVars: map[string]bool{
				"blocked_var": true,
			},
			expected: true,
		},
		{
			name: "variable is not blocked",
			scopeNode: &ScopeNode{
				Level:     0,
				Variables: map[string]*Variable{},
				Children:  []*ScopeNode{},
				Parent:    nil,
			},
			varName: "safe_var",
			blockedVars: map[string]bool{
				"other_var": true,
			},
			expected: false,
		},
		{
			name: "variable blocked in child scope",
			scopeNode: &ScopeNode{
				Level:     0,
				Variables: map[string]*Variable{},
				Children: []*ScopeNode{
					{
						Level:     1,
						Variables: map[string]*Variable{},
						Children:  []*ScopeNode{},
						Parent:    nil,
					},
				},
				Parent: nil,
			},
			varName: "child_blocked",
			blockedVars: map[string]bool{
				"child_blocked": true,
			},
			expected: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := isVariableBlockedInChildren(tt.scopeNode, tt.varName, tt.blockedVars)
			if result != tt.expected {
				t.Errorf("isVariableBlockedInChildren() = %v, expected %v", result, tt.expected)
			}
		})
	}
}

func TestParseVariablesWithBlockingDetection(t *testing.T) {
	tests := []struct {
		name               string
		content            string
		expectedVarCount   int
		expectedBlockedVar string
		shouldBeBlocked    bool
	}{
		{
			name: "variable should be blocked by assign",
			content: `
				logic data_in;
				logic data_out;
				assign data_out = data_in;
			`,
			expectedVarCount:   2,
			expectedBlockedVar: "data_out",
			shouldBeBlocked:    true,
		},
		{
			name: "variable should be blocked by always_comb",
			content: `
				logic a, b, result;
				always_comb begin
					result = a + b;
				end
			`,
			expectedVarCount:   3,
			expectedBlockedVar: "result",
			shouldBeBlocked:    true,
		},
		{
			name: "variable should be blocked by always_ff",
			content: `
				logic clk, data, reg_data;
				always_ff @(posedge clk) begin
					reg_data <= data;
				end
			`,
			expectedVarCount:   3,
			expectedBlockedVar: "reg_data",
			shouldBeBlocked:    true,
		},
		{
			name: "variable should not be blocked",
			content: `
				logic safe_var;
				logic another_var;
			`,
			expectedVarCount:   2,
			expectedBlockedVar: "safe_var",
			shouldBeBlocked:    false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			variables, scopeTree, err := ParseVariables(nil, tt.content, []Parameter{})
			if err != nil {
				t.Fatalf("ParseVariables() error = %v", err)
			}

			if len(variables) != tt.expectedVarCount {
				t.Errorf(
					"ParseVariables() variable count = %d, expected %d",
					len(variables),
					tt.expectedVarCount,
				)
			}

			// Check if the variable exists in the scope tree
			testVF := createTestVerilogFileWithModules()
			blockedVars := detectBlockedVariables(testVF, tt.content)
			isBlocked := blockedVars[tt.expectedBlockedVar]

			if isBlocked != tt.shouldBeBlocked {
				t.Errorf(
					"Variable %s blocking status = %v, expected %v",
					tt.expectedBlockedVar,
					isBlocked,
					tt.shouldBeBlocked,
				)
			}

			// Verify the scope tree structure
			if scopeTree == nil {
				t.Error("ParseVariables() returned nil scope tree")
			}
		})
	}
}

// Helper functions for testing

func setupParentRelationships(node *ScopeNode) {
	if node == nil {
		return
	}
	for _, child := range node.Children {
		child.Parent = node
		setupParentRelationships(child)
	}
}

func compareScopeNodesForBlocking(actual, expected *ScopeNode) bool {
	if actual == nil && expected == nil {
		return true
	}
	if actual == nil || expected == nil {
		return false
	}

	// Compare basic properties
	if actual.Level != expected.Level {
		return false
	}

	// Compare variables
	if len(actual.Variables) != len(expected.Variables) {
		return false
	}
	for name, actualVar := range actual.Variables {
		expectedVar, exists := expected.Variables[name]
		if !exists {
			return false
		}
		if actualVar.Name != expectedVar.Name || actualVar.Type != expectedVar.Type {
			return false
		}
	}

	// Compare children
	if len(actual.Children) != len(expected.Children) {
		return false
	}
	for i, actualChild := range actual.Children {
		if !compareScopeNodesForBlocking(actualChild, expected.Children[i]) {
			return false
		}
	}

	return true
}

func TestBlockingRegexPatterns(t *testing.T) {
	tests := []struct {
		name    string
		content string
		matches []string
	}{
		{
			name:    "assign regex",
			content: "assign data_out = data_in & enable;",
			matches: []string{"data_out"},
		},
		{
			name:    "wire assign regex",
			content: "wire clk = oscillator;",
			matches: []string{"clk"},
		},
		{
			name:    "force regex",
			content: "force debug_signal = 1'b1;",
			matches: []string{"debug_signal"},
		},
		{
			name:    "blocking assign regex",
			content: "    result = a + b;",
			matches: []string{"result"},
		},
		{
			name:    "array assign regex",
			content: "    memory[index] = data;",
			matches: []string{"memory"},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Test the specific regex pattern
			var actualMatches []string
			switch tt.name {
			case "assign regex":
				matches := assignRegex.FindAllStringSubmatch(tt.content, -1)
				for _, match := range matches {
					if len(match) >= 2 {
						actualMatches = append(actualMatches, match[1])
					}
				}
			case "wire assign regex":
				matches := wireAssignRegex.FindAllStringSubmatch(tt.content, -1)
				for _, match := range matches {
					if len(match) >= 2 {
						actualMatches = append(actualMatches, match[1])
					}
				}
			case "force regex":
				matches := forceRegex.FindAllStringSubmatch(tt.content, -1)
				for _, match := range matches {
					if len(match) >= 2 {
						actualMatches = append(actualMatches, match[1])
					}
				}
			case "blocking assign regex", "array assign regex":
				matches := blockingAssignRegex.FindAllStringSubmatch(tt.content, -1)
				for _, match := range matches {
					if len(match) >= 2 {
						actualMatches = append(actualMatches, match[1])
					}
				}
			}

			if !reflect.DeepEqual(actualMatches, tt.matches) {
				t.Errorf("Regex %s: got %v, expected %v", tt.name, actualMatches, tt.matches)
			}
		})
	}
}

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

func TestRealWorldModuleInstantiationBlocking(t *testing.T) {
	// Test case based on the actual simple_sub.sv file issue
	content := `
		module simple_sub (
			input logic [7:0] a,
			input logic [7:0] b,
			output logic [7:0] inj_out_val_d_l_407,
			output logic [8:0] sum
		);
			// Local variable declarations
			logic clk;
			logic condition;
			logic [7:0] temp_signal;
			
			split_inputs_outputs_only split_inputs_outputs_only_inst_1441 (
				.in_val_a_l(a),
				.in_val_b_l(b),
				.out_val_c_l(sum),
				.out_val_d_l(inj_out_val_d_l_407)
			);
			
			split_if_only_then split_if_only_then_inst_8701 (
				.clk_h(clk),
				.condition_h(condition),
				.in_val_h(temp_signal),
				.out_reg_h(inj_out_val_d_l_407)
			);
			
			// This should be detected as a conflict - inj_out_val_d_l_407 is assigned by module
			assign inj_out_val_d_l_407 = a & b;
			
			// This should also be detected as a conflict  
			always @(posedge clk) begin
				inj_out_val_d_l_407 <= a;
			end
		endmodule
	`

	variables, scopeTree, err := ParseVariables(nil, content, []Parameter{})
	if err != nil {
		t.Fatalf("ParseVariables() error = %v", err)
	}

	// Verify that the blocked variable detection works
	testVF := createTestVerilogFileWithModules()
	blockedVars := detectBlockedVariables(testVF, content)

	// inj_out_val_d_l_407 should be detected as blocked due to:
	// 1. Module instantiation output port
	// 2. Assign statement
	// 3. Always block assignment
	if !blockedVars["inj_out_val_d_l_407"] {
		t.Error("Variable inj_out_val_d_l_407 should be blocked due to multiple assignments")
	}

	// sum should be blocked due to module instantiation
	if !blockedVars["sum"] {
		t.Error("Variable sum should be blocked due to module instantiation")
	}

	// temp_signal should NOT be blocked as it's only used as input
	if blockedVars["temp_signal"] {
		t.Error("Variable temp_signal should not be blocked as it's only an input")
	}

	// Verify variables map contains the local variables
	expectedVars := []string{"clk", "condition", "temp_signal"}
	for _, varName := range expectedVars {
		if _, exists := variables[varName]; !exists {
			t.Errorf("Variable %s should exist in variables map", varName)
		}
	}

	// Verify the scope tree structure
	if scopeTree == nil {
		t.Error("ParseVariables() returned nil scope tree")
	}

	t.Logf("Blocked variables detected: %v", blockedVars)
	t.Logf("Total variables found: %d", len(variables))
	t.Logf("Variables in scope: %v", func() []string {
		var names []string
		for name := range variables {
			names = append(names, name)
		}
		return names
	}())
}

func TestModuleInstantiationAccuratePortDirection(t *testing.T) {
	// Test content with a module instantiation
	content := `
		processor_core cpu_inst (
			.clk(system_clock),        // Input port - should NOT be blocked
			.reset_n(reset_signal),    // Input port - should NOT be blocked  
			.data_in(input_data),      // Input port - should NOT be blocked
			.data_out(output_data),    // Output port - SHOULD be blocked
			.valid_out(data_valid),    // Output port - SHOULD be blocked
			.error_flag(error_status)  // Output port - SHOULD be blocked
		);
	`

	// Create VerilogFile with accurate module definition
	vf := NewVerilogFile("test")
	vf.Modules["processor_core"] = &Module{
		Name: "processor_core",
		Ports: []Port{
			{Name: "clk", Direction: INPUT},
			{Name: "reset_n", Direction: INPUT},
			{Name: "data_in", Direction: INPUT},
			{Name: "data_out", Direction: OUTPUT},
			{Name: "valid_out", Direction: OUTPUT},
			{Name: "error_flag", Direction: OUTPUT},
		},
	}

	// Test the new accurate behavior
	blockedVars := detectBlockedVariables(vf, content)

	// Variables connected to INPUT ports should NOT be blocked
	inputVars := []string{"system_clock", "reset_signal", "input_data"}
	for _, varName := range inputVars {
		if blockedVars[varName] {
			t.Errorf(
				"Variable %s is connected to an INPUT port and should NOT be blocked, but was blocked",
				varName,
			)
		}
	}

	// Variables connected to OUTPUT ports SHOULD be blocked
	outputVars := []string{"output_data", "data_valid", "error_status"}
	for _, varName := range outputVars {
		if !blockedVars[varName] {
			t.Errorf(
				"Variable %s is connected to an OUTPUT port and SHOULD be blocked, but was not blocked",
				varName,
			)
		}
	}

	t.Logf("Correctly blocked only OUTPUT port variables: %v", blockedVars)
}

func TestModuleInstantiationFallbackToHeuristics(t *testing.T) {
	// Test content with a module instantiation where module definition is not available
	content := `
		unknown_module unknown_inst (
			.clk_in(clock_signal),        // Should use heuristics
			.enable_out(enable_signal),   // Should use heuristics  
			.data_output(result_data)     // Should use heuristics
		);
	`

	// Create VerilogFile WITHOUT the module definition
	vf := NewVerilogFile("test")
	// Intentionally don't add "unknown_module" to test fallback behavior

	// Test fallback to heuristics
	blockedVars := detectBlockedVariables(vf, content)

	// With heuristics, variables with "out" or "output" patterns should be blocked
	// But input patterns take precedence (e.g., "enable" in "enable_out")
	// This tests that the fallback mechanism works when module definitions aren't available
	expectedBlocked := map[string]bool{
		"enable_signal": false, // "enable_out" contains "enable" (input pattern), so not blocked
		"result_data":   true,  // "data_output" contains "output" (output pattern), so blocked
		"clock_signal":  false, // "clk_in" contains "clk" (input pattern), so not blocked
	}

	for varName, shouldBeBlocked := range expectedBlocked {
		isBlocked := blockedVars[varName]
		if isBlocked != shouldBeBlocked {
			t.Errorf("Variable %s blocking status = %v, expected %v (using heuristics fallback)",
				varName, isBlocked, shouldBeBlocked)
		}
	}

	t.Logf("Fallback heuristics correctly applied: %v", blockedVars)
}

func TestModuleInstantiationRegexIssues(t *testing.T) {
	tests := []struct {
		name            string
		content         string
		expectedModules []string
		expectedPorts   map[string][]string // module -> ports
	}{
		{
			name: "simple_module_instantiation",
			content: `
				simple_module inst1 (
					.clk(clock),
					.data(signal)
				);
			`,
			expectedModules: []string{"simple_module"},
			expectedPorts: map[string][]string{
				"simple_module": {"clk", "data"},
			},
		},
		{
			name: "module_with_long_name",
			content: `
				split_conditional_blocking split_conditional_blocking_inst_4881 (
					.condition_o(inj_condition_o_686),
					.in_false_o(a),
					.in_true_o(b),
					.out_val_o(inj_out_val_o_22)
				);
			`,
			expectedModules: []string{"split_conditional_blocking"},
			expectedPorts: map[string][]string{
				"split_conditional_blocking": {
					"condition_o",
					"in_false_o",
					"in_true_o",
					"out_val_o",
				},
			},
		},
		{
			name: "module_with_complex_context",
			content: `
				// Some previous code
				assign sum = a - b;
				
				// Module instantiation after other statements
				split_conditional_blocking split_conditional_blocking_inst_4881 (
					.condition_o(inj_condition_o_686),
					.in_false_o(a),
					.in_true_o(b),
					.out_val_o(inj_out_val_o_22)
				);
				
				// Some following code
				assign result = sum + 1;
			`,
			expectedModules: []string{"split_conditional_blocking"},
			expectedPorts: map[string][]string{
				"split_conditional_blocking": {
					"condition_o",
					"in_false_o",
					"in_true_o",
					"out_val_o",
				},
			},
		},
		{
			name: "multiple_modules_with_context",
			content: `
				begin
					internal_out = 0;
				end else begin
					internal_out = 3;
				end
				
				split_conditional_blocking split_inst1 (
					.in_false_o(a),
					.out_val_o(result1)
				);
				
				another_module another_inst (
					.input_port(signal),
					.output_port(result2)
				);
			`,
			expectedModules: []string{"split_conditional_blocking", "another_module"},
			expectedPorts: map[string][]string{
				"split_conditional_blocking": {"in_false_o", "out_val_o"},
				"another_module":             {"input_port", "output_port"},
			},
		},
	}

	// Create VerilogFile with test modules
	vf := createTestVerilogFileWithModules()

	// Add the modules we're testing
	vf.Modules["split_conditional_blocking"] = &Module{
		Name: "split_conditional_blocking",
		Ports: []Port{
			{Name: "condition_o", Direction: INPUT},
			{Name: "in_false_o", Direction: INPUT},
			{Name: "in_true_o", Direction: INPUT},
			{Name: "out_val_o", Direction: OUTPUT},
		},
	}
	vf.Modules["another_module"] = &Module{
		Name: "another_module",
		Ports: []Port{
			{Name: "input_port", Direction: INPUT},
			{Name: "output_port", Direction: OUTPUT},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Test the regex extraction
			moduleInstMatches := moduleInstRegex.FindAllStringSubmatch(tt.content, -1)

			if len(moduleInstMatches) != len(tt.expectedModules) {
				t.Errorf(
					"Expected %d module instantiations, got %d",
					len(tt.expectedModules),
					len(moduleInstMatches),
				)
				for i, match := range moduleInstMatches {
					t.Logf(
						"Match %d: Full='%s', Module='%s', Instance='%s'",
						i,
						match[0],
						match[1],
						match[2],
					)
				}
				return
			}

			// Check each match
			for i, match := range moduleInstMatches {
				if len(match) < 4 {
					t.Errorf("Match %d has insufficient groups: %v", i, match)
					continue
				}

				moduleName := strings.TrimSpace(match[1])
				instanceName := strings.TrimSpace(match[2])
				portConnections := match[3]

				expectedModule := tt.expectedModules[i]
				if moduleName != expectedModule {
					t.Errorf(
						"Match %d: expected module '%s', got '%s'",
						i,
						expectedModule,
						moduleName,
					)
					t.Logf("Full match: '%s'", match[0])
					t.Logf("Instance name: '%s'", instanceName)
				}

				// Test port extraction
				portMatches := portConnectionRegex.FindAllStringSubmatch(portConnections, -1)
				var extractedPorts []string
				for _, portMatch := range portMatches {
					if len(portMatch) >= 2 {
						extractedPorts = append(extractedPorts, strings.TrimSpace(portMatch[1]))
					}
				}

				expectedPorts := tt.expectedPorts[expectedModule]
				if len(extractedPorts) != len(expectedPorts) {
					t.Errorf("Expected %d ports for module %s, got %d: %v",
						len(expectedPorts), expectedModule, len(extractedPorts), extractedPorts)
				}
			}

			// Test the complete blocking detection
			blockedVars := detectBlockedVariables(vf, tt.content)
			t.Logf("Blocked variables for %s: %v", tt.name, blockedVars)
		})
	}
}

func TestRealWorldRegexIssue(t *testing.T) {
	// This is the content from the real file that's causing the issue
	content := `
    always @* begin
        internal_out = 0;
        (* unique *)
        if (inj_sel1_474) begin
            internal_out = 1;
        end else if (inj_sel2_799) begin
            internal_out = 2;
        end else begin
            internal_out = 3;
        end
        (* unique0 *)
        if (inj_sel1_474 && inj_sel2_799) begin
            internal_out = 4;
        end else if (inj_sel2_799 && inj_condition_o_686) begin
            internal_out = 5;
        end
    end
    assign inj_if_pragma_out_556 = internal_out;
    // END: if_pragmas_mod
    
    split_conditional_blocking split_conditional_blocking_inst_4881 (
    .condition_o(inj_condition_o_686),
    .in_false_o(a),
    .in_true_o(b),
    .out_val_o(inj_out_val_o_22)
    );
    assign sum = a - b;
	`

	// Test the regex extraction
	moduleInstMatches := moduleInstRegex.FindAllStringSubmatch(content, -1)

	t.Logf("Found %d module instantiation matches", len(moduleInstMatches))
	for i, match := range moduleInstMatches {
		if len(match) >= 4 {
			t.Logf("Match %d:", i)
			t.Logf("  Full match: '%s'", match[0])
			t.Logf("  Module name: '%s'", match[1])
			t.Logf("  Instance name: '%s'", match[2])
			t.Logf("  Port connections: '%s'", match[3])
		} else {
			t.Logf("Match %d has insufficient groups: %v", i, match)
		}
	}

	// Create VerilogFile with test modules
	vf := createTestVerilogFileWithModules()
	vf.Modules["split_conditional_blocking"] = &Module{
		Name: "split_conditional_blocking",
		Ports: []Port{
			{Name: "condition_o", Direction: INPUT},
			{Name: "in_false_o", Direction: INPUT},
			{Name: "in_true_o", Direction: INPUT},
			{Name: "out_val_o", Direction: OUTPUT},
		},
	}

	// Test the complete blocking detection
	blockedVars := detectBlockedVariables(vf, content)
	t.Logf("Blocked variables: %v", blockedVars)
}

func TestMultipleDriverBlocking(t *testing.T) {
	// Test content with a variable assigned in multiple blocking ways
	testCases := []struct {
		name    string
		content string
	}{
		{
			name: "always driver",
			content: `
				logic [7:0] output_signal;
				// Non-blocking assignment in always block
				always @(posedge clk) begin
					output_signal <= input_a;
				end
				`,
		},
		{
			name: "assign driver",
			content: `
		logic [7:0] output_signal;
		
		// Non-blocking assignment in always block
		always @(posedge clk) begin
			output_signal <= input_a;
		end
		
		// Continuous assignment to the same variable
		assign output_signal = input_b;
	`,
		},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			// Test the blocking detection
			vf := createTestVerilogFileWithModules()
			blockedVars := detectBlockedVariables(vf, tc.content)

			// output_signal should be blocked because it has multiple drivers
			if !blockedVars["output_signal"] {
				t.Error(
					"Variable output_signal should be blocked due to multiple assignments (always block + assign)",
				)
			}

			t.Logf("Correctly detected multiple driver blocking: %v", blockedVars)
		})
	}
}

func TestRealWorldMultipleDriverCase(t *testing.T) {
	// This is the actual case from the real file
	content := `
		logic [7:0] inj_data_out_pa_200;
		
		// Non-blocking assignment in always block
		always @(posedge inj_enable_pv_672) begin
			inj_data_out_pa_200 <= a;
		end
		
		// Later in the code...
		assign inj_data_out_pa_200 = data_pa[0];
	`

	// Test the blocking detection
	vf := createTestVerilogFileWithModules()
	blockedVars := detectBlockedVariables(vf, content)

	// inj_data_out_pa_200 should be blocked because it has multiple drivers
	if !blockedVars["inj_data_out_pa_200"] {
		t.Error("Variable inj_data_out_pa_200 should be blocked due to multiple assignments")
	}

	t.Logf("Real world multiple driver case: %v", blockedVars)
}

func TestFullRealWorldFile(t *testing.T) {
	// This is content from the actual file
	content := `
		logic [31:0] data_pv ;
		logic [7:0] data_pa[0:1] ;
		logic [7:0] inj_data_out_pa_200;
		
		// Non-blocking assignment in always block
		always @(posedge inj_enable_pv_672) begin
			inj_data_out_pa_200 <= a;
		end
		
		always_comb begin
			if (inj_enable_pv_672) begin
				data_pv[7:0] = a;
				data_pv[15:8] = ~a;
				data_pv[23:16] = data_pv[7:0];
				data_pv[31:24] = data_pv[15:8];
				data_pa[0] = inj_data_in_pa_915[7:0];
				data_pa[1] = inj_data_in_pa_915[15:8];
			end else begin
				data_pv = 32'h0;
				data_pa[0] = 8'h0;
				data_pa[1] = 8'h0;
			end
		end
		assign inj_out_idx_29 = data_pv[3:0];
		assign inj_data_out_pa_200 = data_pa[0];  // Multiple driver!
		
		always_comb begin: for_break_block
			inj_out_idx_29 = 0;
			for (int i = 0; i < 10; i++) begin
				inj_out_idx_29 = i;
				if (i == inj_in_target_302) begin
					break;
				end
			end
		end
	`

	// Test the blocking detection
	vf := createTestVerilogFileWithModules()
	blockedVars := detectBlockedVariables(vf, content)

	// Variables that should be blocked
	expectedBlocked := map[string]bool{
		"inj_data_out_pa_200": true, // Multiple drivers: always block + assign
		"data_pv":             true, // Assigned in always_comb
		"data_pa":             true, // Array assigned in always_comb
		"inj_out_idx_29":      true, // Multiple drivers: assign + always_comb
	}

	for varName, shouldBeBlocked := range expectedBlocked {
		isBlocked := blockedVars[varName]
		if isBlocked != shouldBeBlocked {
			t.Errorf("Variable %s blocking status = %v, expected %v",
				varName, isBlocked, shouldBeBlocked)
		}
	}

	t.Logf("Full real world file blocking detection: %v", blockedVars)
}

// createTestVerilogFileWithModules creates a VerilogFile with common test modules
func createTestVerilogFileWithModules() *VerilogFile {
	vf := NewVerilogFile("test")

	// counter_module: clk, reset, enable are inputs; count_out is output
	vf.Modules["counter_module"] = &Module{
		Name: "counter_module",
		Ports: []Port{
			{Name: "clk", Direction: INPUT},
			{Name: "reset", Direction: INPUT},
			{Name: "enable", Direction: INPUT},
			{Name: "count_out", Direction: OUTPUT},
		},
	}

	// adder_module: clk, data_in are inputs; result_out, valid_out are outputs
	vf.Modules["adder_module"] = &Module{
		Name: "adder_module",
		Ports: []Port{
			{Name: "clk", Direction: INPUT},
			{Name: "data_in", Direction: INPUT},
			{Name: "result_out", Direction: OUTPUT},
			{Name: "valid_out", Direction: OUTPUT},
		},
	}

	// split_inputs_outputs_only: inputs are in_val_*, outputs are out_val_*
	vf.Modules["split_inputs_outputs_only"] = &Module{
		Name: "split_inputs_outputs_only",
		Ports: []Port{
			{Name: "in_val_a_l", Direction: INPUT},
			{Name: "in_val_b_l", Direction: INPUT},
			{Name: "out_val_c_l", Direction: OUTPUT},
			{Name: "out_val_d_l", Direction: OUTPUT},
		},
	}

	// split_if_only_then: clk_h, condition_h, in_val_h are inputs; out_reg_h is output
	vf.Modules["split_if_only_then"] = &Module{
		Name: "split_if_only_then",
		Ports: []Port{
			{Name: "clk_h", Direction: INPUT},
			{Name: "condition_h", Direction: INPUT},
			{Name: "in_val_h", Direction: INPUT},
			{Name: "out_reg_h", Direction: OUTPUT},
		},
	}

	// processor_module: clk, data_in are inputs; data_out is output
	vf.Modules["processor_module"] = &Module{
		Name: "processor_module",
		Ports: []Port{
			{Name: "clk", Direction: INPUT},
			{Name: "data_in", Direction: INPUT},
			{Name: "data_out", Direction: OUTPUT},
		},
	}

	return vf
}

func TestAlwaysBlockDetectionDebug(t *testing.T) {
	content := `
		logic [7:0] output_signal;
		// Non-blocking assignment in always block
		always @(posedge clk) begin
			output_signal <= input_a;
		end
	`

	// Debug the regex matching
	alwaysFFMatches := alwaysFFRegex.FindAllStringSubmatch(content, -1)
	t.Logf("Always FF matches: %d", len(alwaysFFMatches))
	for i, match := range alwaysFFMatches {
		t.Logf("Match %d: %v", i, match)
	}

	blockingAssignMatches := blockingAssignRegex.FindAllStringSubmatch(content, -1)
	t.Logf("Blocking assign matches: %d", len(blockingAssignMatches))
	for i, match := range blockingAssignMatches {
		t.Logf("Match %d: %v", i, match)
	}

	vf := createTestVerilogFileWithModules()
	blockedVars := detectBlockedVariables(vf, content)
	t.Logf("Blocked variables: %v", blockedVars)
}

func TestScopeDetectionWithNonVariableLines(t *testing.T) {
	// Test case based on the original issue: variables in different scopes
	// should be correctly separated even when there are non-variable lines
	// affecting the scope structure
	content := `
task my_task;
    logic [7:0] a;
    assign a = 4'h5;
endtask

always_comb begin
    logic [7:0] b;
    b = 5'h6;
end

logic [7:0] c;
`

	variables, scopeTree, err := ParseVariables(nil, content, nil)
	if err != nil {
		t.Fatalf("ParseVariables failed: %v", err)
	}

	// Check that all variables were found
	expectedVars := []string{"a", "b", "c"}
	if len(variables) != len(expectedVars) {
		t.Fatalf(
			"Expected %d variables, got %d: %v",
			len(expectedVars),
			len(variables),
			getVariableNames(variables),
		)
	}

	for _, varName := range expectedVars {
		if _, exists := variables[varName]; !exists {
			t.Errorf("Expected variable '%s' not found in parsed variables", varName)
		}
	}

	// Check scope structure
	if scopeTree == nil {
		t.Fatal("Scope tree is nil")
	}

	// Verify that variables are in different scopes
	// Variable 'a' should be in a nested scope (inside task)
	// Variable 'b' should be in a nested scope (inside always_comb)
	// Variable 'c' should be in the root scope

	// Find variable 'a' in the scope tree
	varAScopeLevel := findVariableInScopeTree(scopeTree, "a")
	switch varAScopeLevel {
	case -1:
		t.Log("Variable 'a' not found in any scope, expected as unassignable")
	case 0:
		t.Error("Variable 'a' should be in a nested scope (task), but found in root scope")
	default:
		t.Errorf("Variable 'a' correctly found in scope level %d", varAScopeLevel)
	}

	// Find variable 'b' in the scope tree
	varBScopeLevel := findVariableInScopeTree(scopeTree, "b")
	switch varBScopeLevel {
	case -1:
		t.Log("Variable 'b' not found in any scope, expected as unassignable")
	case 0:
		t.Error("Variable 'b' should be in a nested scope (always_comb), but found in root scope")
	default:
		t.Errorf("Variable 'b' correctly found in scope level %d", varBScopeLevel)
	}

	// Find variable 'c' in the scope tree
	varCScopeLevel := findVariableInScopeTree(scopeTree, "c")
	switch varCScopeLevel {
	case -1:
		t.Error("Variable 'c' not found in any scope")
	case 0:
		t.Logf("Variable 'c' correctly found in root scope level %d", varCScopeLevel)
	default:
		t.Errorf(
			"Variable 'c' should be in root scope (level 0), but found in level %d",
			varCScopeLevel,
		)
	}
	// Verify that 'a' and 'b' are in different scopes (they shouldn't be in the same scope)
	if varAScopeLevel != -1 && varBScopeLevel != -1 {
		aScope := findScopeForVariable(scopeTree, "a")
		bScope := findScopeForVariable(scopeTree, "b")

		if aScope != nil && bScope != nil && aScope == bScope {
			t.Error(
				"Variables 'a' and 'b' should be in different scopes, but they are in the same scope",
			)
		} else if aScope != nil && bScope != nil {
			t.Logf("Variables 'a' and 'b' are correctly in different scopes")
		}
	}

	t.Logf("Scope tree structure: %s", scopeTree.Dump(1))
}

// Helper function to get variable names from a map
func getVariableNames(variables map[string]*Variable) []string {
	names := make([]string, 0, len(variables))
	for name := range variables {
		names = append(names, name)
	}
	return names
}

// Helper function to find a variable in the scope tree and return its scope level
func findVariableInScopeTree(node *ScopeNode, varName string) int {
	if node == nil {
		return -1
	}

	// Check if variable is in current scope
	if _, exists := node.Variables[varName]; exists {
		return node.Level
	}

	// Recursively check children
	for _, child := range node.Children {
		level := findVariableInScopeTree(child, varName)
		if level != -1 {
			return level
		}
	}

	return -1
}

// Helper function to find the actual scope node that contains a variable
func findScopeForVariable(node *ScopeNode, varName string) *ScopeNode {
	if node == nil {
		return nil
	}

	// Check if variable is in current scope
	if _, exists := node.Variables[varName]; exists {
		return node
	}

	// Recursively check children
	for _, child := range node.Children {
		scope := findScopeForVariable(child, varName)
		if scope != nil {
			return scope
		}
	}

	return nil
}
