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
