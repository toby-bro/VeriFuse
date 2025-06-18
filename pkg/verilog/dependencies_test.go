package verilog

import (
	"testing"
)

func TestAddDependency(t *testing.T) { //nolint: gocyclo
	tests := []struct {
		name        string
		childName   string
		parentNames []string
		setup       func(*VerilogFile) // Optional setup function
		validate    func(*testing.T, *VerilogFile)
	}{
		{
			name:        "Add single dependency to empty map",
			childName:   "child1",
			parentNames: []string{"parent1"},
			validate: func(t *testing.T, vf *VerilogFile) {
				if len(vf.DependencyMap) != 2 {
					t.Errorf("Expected 2 nodes in dependency map, got %d", len(vf.DependencyMap))
				}

				childNode := vf.DependencyMap["child1"]
				if childNode == nil {
					t.Fatal("Child node not found")
				}
				if len(childNode.DependsOn) != 1 || childNode.DependsOn[0] != "parent1" {
					t.Errorf("Expected child1 to depend on parent1, got %v", childNode.DependsOn)
				}

				parentNode := vf.DependencyMap["parent1"]
				if parentNode == nil {
					t.Fatal("Parent node not found")
				}
				if len(parentNode.DependedBy) != 1 || parentNode.DependedBy[0] != "child1" {
					t.Errorf(
						"Expected parent1 to be depended by child1, got %v",
						parentNode.DependedBy,
					)
				}
			},
		},
		{
			name:        "Add multiple dependencies",
			childName:   "child1",
			parentNames: []string{"parent1", "parent2", "parent3"},
			validate: func(t *testing.T, vf *VerilogFile) {
				if len(vf.DependencyMap) != 4 {
					t.Errorf("Expected 4 nodes in dependency map, got %d", len(vf.DependencyMap))
				}

				childNode := vf.DependencyMap["child1"]
				if childNode == nil {
					t.Fatal("Child node not found")
				}
				expectedParents := []string{"parent1", "parent2", "parent3"}
				if len(childNode.DependsOn) != len(expectedParents) {
					t.Errorf(
						"Expected child1 to depend on %d parents, got %d",
						len(expectedParents),
						len(childNode.DependsOn),
					)
				}

				for _, parent := range expectedParents {
					found := false
					for _, dep := range childNode.DependsOn {
						if dep == parent {
							found = true
							break
						}
					}
					if !found {
						t.Errorf("Expected child1 to depend on %s", parent)
					}

					parentNode := vf.DependencyMap[parent]
					if parentNode == nil {
						t.Fatalf("Parent node %s not found", parent)
					}
					found = false
					for _, dep := range parentNode.DependedBy {
						if dep == "child1" {
							found = true
							break
						}
					}
					if !found {
						t.Errorf("Expected %s to be depended by child1", parent)
					}
				}
			},
		},
		{
			name:        "Add duplicate dependency should not create duplicates",
			childName:   "child1",
			parentNames: []string{"parent1"},
			setup: func(vf *VerilogFile) {
				// Add the same dependency first
				vf.AddDependency("child1", "parent1")
			},
			validate: func(t *testing.T, vf *VerilogFile) {
				childNode := vf.DependencyMap["child1"]
				if childNode == nil {
					t.Fatal("Child node not found")
				}
				if len(childNode.DependsOn) != 1 {
					t.Errorf(
						"Expected child1 to have exactly 1 dependency, got %d",
						len(childNode.DependsOn),
					)
				}

				parentNode := vf.DependencyMap["parent1"]
				if parentNode == nil {
					t.Fatal("Parent node not found")
				}
				if len(parentNode.DependedBy) != 1 {
					t.Errorf(
						"Expected parent1 to be depended by exactly 1 child, got %d",
						len(parentNode.DependedBy),
					)
				}
			},
		},
		{
			name:        "Empty child name should be ignored",
			childName:   "",
			parentNames: []string{"parent1"},
			validate: func(t *testing.T, vf *VerilogFile) {
				if len(vf.DependencyMap) != 0 {
					t.Errorf("Expected empty dependency map, got %d nodes", len(vf.DependencyMap))
				}
			},
		},
		{
			name:        "Empty parent names should be ignored",
			childName:   "child1",
			parentNames: []string{"", "parent1", ""},
			validate: func(t *testing.T, vf *VerilogFile) {
				if len(vf.DependencyMap) != 2 {
					t.Errorf("Expected 2 nodes in dependency map, got %d", len(vf.DependencyMap))
				}

				childNode := vf.DependencyMap["child1"]
				if childNode == nil {
					t.Fatal("Child node not found")
				}
				if len(childNode.DependsOn) != 1 || childNode.DependsOn[0] != "parent1" {
					t.Errorf(
						"Expected child1 to depend only on parent1, got %v",
						childNode.DependsOn,
					)
				}
			},
		},
		{
			name:        "Self-dependency should be ignored",
			childName:   "module1",
			parentNames: []string{"module1", "parent1"},
			validate: func(t *testing.T, vf *VerilogFile) {
				if len(vf.DependencyMap) != 2 {
					t.Errorf("Expected 2 nodes in dependency map, got %d", len(vf.DependencyMap))
				}

				childNode := vf.DependencyMap["module1"]
				if childNode == nil {
					t.Fatal("Child node not found")
				}
				if len(childNode.DependsOn) != 1 || childNode.DependsOn[0] != "parent1" {
					t.Errorf(
						"Expected module1 to depend only on parent1 (not itself), got %v",
						childNode.DependsOn,
					)
				}
			},
		},
		{
			name:        "Add dependency to existing node",
			childName:   "child1",
			parentNames: []string{"parent2"},
			setup: func(vf *VerilogFile) {
				// Create existing child node with one dependency
				vf.AddDependency("child1", "parent1")
			},
			validate: func(t *testing.T, vf *VerilogFile) {
				childNode := vf.DependencyMap["child1"]
				if childNode == nil {
					t.Fatal("Child node not found")
				}
				if len(childNode.DependsOn) != 2 {
					t.Errorf(
						"Expected child1 to have 2 dependencies, got %d",
						len(childNode.DependsOn),
					)
				}

				expectedParents := []string{"parent1", "parent2"}
				for _, parent := range expectedParents {
					found := false
					for _, dep := range childNode.DependsOn {
						if dep == parent {
							found = true
							break
						}
					}
					if !found {
						t.Errorf("Expected child1 to depend on %s", parent)
					}
				}
			},
		},
		{
			name:        "No parent names provided",
			childName:   "child1",
			parentNames: []string{},
			validate: func(t *testing.T, vf *VerilogFile) {
				if len(vf.DependencyMap) != 1 {
					t.Errorf("Expected 1 node in dependency map, got %d", len(vf.DependencyMap))
				}

				childNode := vf.DependencyMap["child1"]
				if childNode == nil {
					t.Fatal("Child node not found")
				}
				if len(childNode.DependsOn) != 0 {
					t.Errorf("Expected child1 to have no dependencies, got %v", childNode.DependsOn)
				}
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Create a new VerilogFile for each test
			vf := NewVerilogFile("test")

			// Run setup if provided
			if tt.setup != nil {
				tt.setup(vf)
			}

			// Call the method under test
			vf.AddDependency(tt.childName, tt.parentNames...)

			// Validate the result
			tt.validate(t, vf)
		})
	}
}

func TestAddDependency_NilDependencyMap(t *testing.T) {
	// Test that AddDependency initializes the map if it's nil
	vf := &VerilogFile{
		Name:          "test",
		DependencyMap: nil, // Explicitly set to nil
	}

	vf.AddDependency("child1", "parent1")

	if vf.DependencyMap == nil {
		t.Fatal("DependencyMap should be initialized")
	}

	if len(vf.DependencyMap) != 2 {
		t.Errorf("Expected 2 nodes in dependency map, got %d", len(vf.DependencyMap))
	}
}

func TestAddDependency_ComplexDependencyGraph(t *testing.T) {
	// Test building a more complex dependency graph
	vf := NewVerilogFile("test")

	// Build a dependency graph:
	// A depends on B, C
	// B depends on D
	// C depends on D, E
	// F depends on A (making F depend transitively on B, C, D, E)

	vf.AddDependency("A", "B", "C")
	vf.AddDependency("B", "D")
	vf.AddDependency("C", "D", "E")
	vf.AddDependency("F", "A")

	// Validate the complete graph
	expectedNodes := []string{"A", "B", "C", "D", "E", "F"}
	if len(vf.DependencyMap) != len(expectedNodes) {
		t.Errorf(
			"Expected %d nodes in dependency map, got %d",
			len(expectedNodes),
			len(vf.DependencyMap),
		)
	}

	// Check A's dependencies
	nodeA := vf.DependencyMap["A"]
	if nodeA == nil {
		t.Fatal("Node A not found")
	}
	if len(nodeA.DependsOn) != 2 {
		t.Errorf("Expected A to depend on 2 nodes, got %d", len(nodeA.DependsOn))
	}
	if len(nodeA.DependedBy) != 1 || nodeA.DependedBy[0] != "F" {
		t.Errorf("Expected A to be depended by F, got %v", nodeA.DependedBy)
	}

	// Check D's dependents (should be depended by both B and C)
	nodeD := vf.DependencyMap["D"]
	if nodeD == nil {
		t.Fatal("Node D not found")
	}
	if len(nodeD.DependedBy) != 2 {
		t.Errorf("Expected D to be depended by 2 nodes, got %d", len(nodeD.DependedBy))
	}
	expectedDependents := []string{"B", "C"}
	for _, expected := range expectedDependents {
		found := false
		for _, actual := range nodeD.DependedBy {
			if actual == expected {
				found = true
				break
			}
		}
		if !found {
			t.Errorf("Expected D to be depended by %s", expected)
		}
	}
}

// TestClassInstantiationDependencyDetection tests that class instantiations within modules are detected as dependencies
func TestClassInstantiationDependencyDetection(t *testing.T) { // nolint: gocyclo
	testContent := `
class MySimpleClass;
    int data;
    function new(int val);
        data = val;
    endfunction
    function int getData();
        return data;
    endfunction
endclass

class BaseClass;
    int base_member;
    function new(int val);
        base_member = val;
    endfunction
    function int get_base();
        return base_member;
    endfunction
endclass

class DerivedClass extends BaseClass;
    int derived_member;
    function new(int b_val, int d_val);
        super.new(b_val);
        derived_member = d_val;
    endfunction
    function int get_derived();
        return derived_member;
    endfunction
    function int sum_members();
        return base_member + derived_member;
    endfunction
endclass

module Class_Usage (
    input wire trigger_in,
    output reg status_out
);
    function automatic int instantiate_and_use_class(input int val);
        MySimpleClass obj = new(val);
        return obj.getData();
    endfunction
    
    always_comb begin
        int temp_val;
        if (trigger_in) begin
            temp_val = instantiate_and_use_class(100);
        end else begin
            temp_val = instantiate_and_use_class(200);
        end
        status_out = (temp_val == 100) || (temp_val == 200);
    end
endmodule

module class_basic_mod (
    input int input_val,
    output int output_val
);
    MySimpleClass inst;
    int temp_data;
    always_comb begin
        inst = new(input_val);
        temp_data = inst.getData();
    end
    assign output_val = temp_data;
endmodule

module class_extends_mod (
    input int derived_val_i,
    output int result_o,
    input int base_val_i
);
    DerivedClass derived_instance;
    int calculation_result;
    always_comb begin
        derived_instance = new(base_val_i, derived_val_i);
        calculation_result = derived_instance.sum_members();
    end
    assign result_o = calculation_result;
endmodule

module ModuleWithExtendedClass (
    input logic base_in,
    output logic derived_out
);
    DerivedClass derived_instance;
    always_comb begin
        derived_instance = new(base_in, 1'b1);
        derived_out = derived_instance.base_member && derived_instance.derived_member;
    end
endmodule
`

	svFile, err := ParseVerilog(testContent, 0)
	if err != nil {
		t.Fatalf("Failed to parse test content: %v", err)
	}

	// Test 1: Verify all classes were parsed
	expectedClasses := []string{"MySimpleClass", "BaseClass", "DerivedClass"}
	if len(svFile.Classes) != len(expectedClasses) {
		t.Errorf("Expected %d classes, got %d", len(expectedClasses), len(svFile.Classes))
	}

	for _, className := range expectedClasses {
		if _, exists := svFile.Classes[className]; !exists {
			t.Errorf("Expected class %s to be parsed", className)
		}
	}

	// Test 2: Verify all modules were parsed
	expectedModules := []string{
		"Class_Usage",
		"class_basic_mod",
		"class_extends_mod",
		"ModuleWithExtendedClass",
	}
	if len(svFile.Modules) != len(expectedModules) {
		t.Errorf("Expected %d modules, got %d", len(expectedModules), len(svFile.Modules))
	}

	for _, moduleName := range expectedModules {
		if _, exists := svFile.Modules[moduleName]; !exists {
			t.Errorf("Expected module %s to be parsed", moduleName)
		}
	}

	// Test 3: Verify class inheritance dependency (DerivedClass extends BaseClass)
	if deps, exists := svFile.DependencyMap["DerivedClass"]; exists {
		found := false
		for _, dep := range deps.DependsOn {
			if dep == "BaseClass" {
				found = true
				break
			}
		}
		if !found {
			t.Error("Expected DerivedClass to depend on BaseClass (inheritance dependency)")
		}
	} else {
		t.Error("Expected DerivedClass to be found in dependency map")
	}

	// Test 4: Verify Class_Usage module depends on MySimpleClass (class instantiation in function)
	if deps, exists := svFile.DependencyMap["Class_Usage"]; exists {
		found := false
		for _, dep := range deps.DependsOn {
			if dep == "MySimpleClass" {
				found = true
				break
			}
		}
		if !found {
			t.Error(
				"Expected Class_Usage to depend on MySimpleClass (class instantiation dependency)",
			)
		}
	} else {
		t.Error("Expected Class_Usage to be found in dependency map")
	}

	// Test 5: Verify class_basic_mod depends on MySimpleClass (direct class instantiation)
	if deps, exists := svFile.DependencyMap["class_basic_mod"]; exists {
		found := false
		for _, dep := range deps.DependsOn {
			if dep == "MySimpleClass" {
				found = true
				break
			}
		}
		if !found {
			t.Error(
				"Expected class_basic_mod to depend on MySimpleClass (class variable instantiation dependency)",
			)
		}
	} else {
		t.Error("Expected class_basic_mod to be found in dependency map")
	}

	// Test 6: Verify class_extends_mod depends on DerivedClass
	if deps, exists := svFile.DependencyMap["class_extends_mod"]; exists {
		found := false
		for _, dep := range deps.DependsOn {
			if dep == "DerivedClass" {
				found = true
				break
			}
		}
		if !found {
			t.Error(
				"Expected class_extends_mod to depend on DerivedClass (derived class instantiation dependency)",
			)
		}
	} else {
		t.Error("Expected class_extends_mod to be found in dependency map")
	}

	// Test 7: Verify ModuleWithExtendedClass depends on DerivedClass
	if deps, exists := svFile.DependencyMap["ModuleWithExtendedClass"]; exists {
		found := false
		for _, dep := range deps.DependsOn {
			if dep == "DerivedClass" {
				found = true
				break
			}
		}
		if !found {
			t.Error(
				"Expected ModuleWithExtendedClass to depend on DerivedClass (extended class usage dependency)",
			)
		}
	} else {
		t.Error("Expected ModuleWithExtendedClass to be found in dependency map")
	}

	// Test 8: Verify that class dependencies are transitively resolved
	// Since class_extends_mod uses DerivedClass, and DerivedClass extends BaseClass,
	// we should check that the transitive dependencies can be resolved correctly through the snippets system
	// This is more of an integration test but demonstrates the full dependency chain

	// Test 9: Test multiple class instantiations in the same module don't create duplicates
	multiClassContent := `
class ClassA;
    int data_a;
    function new(int val);
        data_a = val;
    endfunction
endclass

class ClassB;
    int data_b;
    function new(int val);
        data_b = val;
    endfunction
endclass

module multi_class_module (
    input int input_a,
    input int input_b,
    output int output_sum
);
    ClassA inst_a;
    ClassB inst_b;
    int sum_temp;
    
    always_comb begin
        inst_a = new(input_a);
        inst_b = new(input_b);
        sum_temp = inst_a.data_a + inst_b.data_b;
    end
    
    assign output_sum = sum_temp;
endmodule
`

	svFile2, err := ParseVerilog(multiClassContent, 0)
	if err != nil {
		t.Fatalf("Failed to parse multi-class test content: %v", err)
	}

	// Verify multi_class_module depends on both ClassA and ClassB
	if deps, exists := svFile2.DependencyMap["multi_class_module"]; exists {
		classAFound := false
		classBFound := false

		for _, dep := range deps.DependsOn {
			if dep == "ClassA" {
				classAFound = true
			}
			if dep == "ClassB" {
				classBFound = true
			}
		}

		if !classAFound {
			t.Error("Expected multi_class_module to depend on ClassA")
		}
		if !classBFound {
			t.Error("Expected multi_class_module to depend on ClassB")
		}

		// Check no duplicates (each class should appear only once in dependencies)
		classACount := 0
		classBCount := 0
		for _, dep := range deps.DependsOn {
			if dep == "ClassA" {
				classACount++
			}
			if dep == "ClassB" {
				classBCount++
			}
		}

		if classACount != 1 {
			t.Errorf("Expected exactly one dependency on ClassA, got %d", classACount)
		}
		if classBCount != 1 {
			t.Errorf("Expected exactly one dependency on ClassB, got %d", classBCount)
		}
	} else {
		t.Error("Expected multi_class_module to be found in dependency map")
	}
}

// TestParameterizedClassInstantiation tests class instantiation with parameters
func TestParameterizedClassInstantiation(t *testing.T) {
	testContent := `
class ParamClass #(parameter int WIDTH = 8);
    logic [WIDTH-1:0] data_array;
    int param_member;
    function new(logic [WIDTH-1:0] arr, int pm);
        data_array = arr;
        param_member = pm;
    endfunction
endclass

module ModuleWithParamClass (
    input int data_val,
    output int param_sum_out
);
    ParamClass #(16) param_instance_16;
    always_comb begin
        logic [15:0] temp_array_16;
        temp_array_16 = $unsigned(data_val);
        param_instance_16 = new(temp_array_16, data_val + 5);
        param_sum_out = param_instance_16.param_member + $unsigned(param_instance_16.data_array[0]);
    end
endmodule
`

	svFile, err := ParseVerilog(testContent, 0)
	if err != nil {
		t.Fatalf("Failed to parse parameterized class test content: %v", err)
	}

	// Verify the parameterized class was parsed
	if _, exists := svFile.Classes["ParamClass"]; !exists {
		t.Error("Expected ParamClass to be parsed")
	}

	// Verify the module was parsed
	if _, exists := svFile.Modules["ModuleWithParamClass"]; !exists {
		t.Error("Expected ModuleWithParamClass to be parsed")
	}

	// Verify ModuleWithParamClass depends on ParamClass
	if deps, exists := svFile.DependencyMap["ModuleWithParamClass"]; exists {
		found := false
		for _, dep := range deps.DependsOn {
			if dep == "ParamClass" {
				found = true
				break
			}
		}
		if !found {
			t.Error(
				"Expected ModuleWithParamClass to depend on ParamClass (parameterized class instantiation dependency)",
			)
		}
	} else {
		t.Error("Expected ModuleWithParamClass to be found in dependency map")
	}
}

// TestClassInstantiationInDifferentScopes tests class instantiation in various SystemVerilog scopes
func TestClassInstantiationInDifferentScopes(t *testing.T) {
	testContent := `
class ScopeTestClass;
    int scope_data;
    function new(int val);
        scope_data = val;
    endfunction
    function int get_data();
        return scope_data;
    endfunction
endclass

module scope_test_module (
    input logic clk,
    input logic enable,
    input int input_data,
    output int output_data
);
    ScopeTestClass global_instance;
    int temp_result;
    
    // Class instantiation in always_comb
    always_comb begin
        ScopeTestClass local_instance;
        if (enable) begin
            local_instance = new(input_data);
            temp_result = local_instance.get_data();
        end else begin
            temp_result = 0;
        end
    end
    
    // Class instantiation in function
    function automatic int process_with_class(input int val);
        ScopeTestClass func_instance;
        func_instance = new(val * 2);
        return func_instance.get_data();
    endfunction
    
    // Class instantiation in task
    task automatic process_task(input int task_val, output int task_result);
        ScopeTestClass task_instance;
        task_instance = new(task_val + 10);
        task_result = task_instance.get_data();
    endtask
    
    always_ff @(posedge clk) begin
        global_instance = new(input_data);
        output_data <= global_instance.get_data() + process_with_class(input_data);
    end
endmodule
`

	svFile, err := ParseVerilog(testContent, 0)
	if err != nil {
		t.Fatalf("Failed to parse scope test content: %v", err)
	}

	// Verify the class was parsed
	if _, exists := svFile.Classes["ScopeTestClass"]; !exists {
		t.Error("Expected ScopeTestClass to be parsed")
	}

	// Verify the module was parsed
	if _, exists := svFile.Modules["scope_test_module"]; !exists {
		t.Error("Expected scope_test_module to be parsed")
	}

	// Verify scope_test_module depends on ScopeTestClass
	if deps, exists := svFile.DependencyMap["scope_test_module"]; exists {
		found := false
		for _, dep := range deps.DependsOn {
			if dep == "ScopeTestClass" {
				found = true
				break
			}
		}
		if !found {
			t.Error(
				"Expected scope_test_module to depend on ScopeTestClass (class instantiation in multiple scopes dependency)",
			)
		}
	} else {
		t.Error("Expected scope_test_module to be found in dependency map")
	}
}
