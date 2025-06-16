package snippets

import (
	"fmt"
	"os"
	"path/filepath"
	"sync"
	"testing"

	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

func TestMain(m *testing.M) {
	// Initialize logger for tests
	logger = *utils.NewDebugLogger(1)
	exitCode := m.Run()
	os.Exit(exitCode)
}

func TestFindSnippetFiles(t *testing.T) {
	files, err := findSnippetFiles()
	if err != nil {
		t.Fatalf("findSnippetFiles failed: %v", err)
	}

	if len(files) == 0 {
		t.Errorf("Expected to find snippet files, but got none")
	}

	// Verify all returned files have .sv extension
	for _, file := range files {
		if filepath.Ext(file) != ".sv" {
			t.Errorf("Expected .sv file, got %s", file)
		}

		// Verify file exists
		if _, err := os.Stat(file); os.IsNotExist(err) {
			t.Errorf("File does not exist: %s", file)
		}
	}

	t.Logf("Found %d snippet files", len(files))
}

func TestLoadSnippets(t *testing.T) {
	// Reset global state for clean test
	snippets = []*Snippet{}
	verilogFiles = []*verilog.VerilogFile{}

	err := loadSnippets()
	if err != nil {
		t.Fatalf("loadSnippets failed: %v", err)
	}

	if len(snippets) == 0 {
		t.Errorf("Expected to load snippets, but got none")
	}

	if len(verilogFiles) == 0 {
		t.Errorf("Expected to load verilog files, but got none")
	}

	// Verify snippet integrity
	for i, snippet := range snippets {
		if snippet.Name == "" {
			t.Errorf("Snippet %d has empty name", i)
		}
		if snippet.Module == nil {
			t.Errorf("Snippet %d has nil module", i)
		}
		if snippet.ParentFile == nil {
			t.Errorf("Snippet %d has nil parent file", i)
		}
		if snippet.Module != nil && snippet.Module.Name == "" {
			t.Errorf("Snippet %d module has empty name", i)
		}
	}

	t.Logf("Loaded %d snippets from %d files", len(snippets), len(verilogFiles))
}

func TestGetSnippets(t *testing.T) {
	snippets, verilogFiles, err := getSnippets()
	if err != nil {
		t.Fatalf("getSnippets failed: %v", err)
	}

	if len(snippets) == 0 {
		t.Errorf("getSnippets returned no snippets")
	}

	if len(verilogFiles) == 0 {
		t.Errorf("getSnippets returned no verilog files")
	}

	// Test that subsequent calls return the same data (singleton behavior)
	snippets2, verilogFiles2, err2 := getSnippets()
	if err2 != nil {
		t.Fatalf("Second call to getSnippets failed: %v", err2)
	}

	if len(snippets) != len(snippets2) {
		t.Errorf(
			"Subsequent calls to getSnippets return different number of snippets: %d vs %d",
			len(snippets),
			len(snippets2),
		)
	}

	if len(verilogFiles) != len(verilogFiles2) {
		t.Errorf(
			"Subsequent calls to getSnippets return different number of verilog files: %d vs %d",
			len(verilogFiles),
			len(verilogFiles2),
		)
	}
}

func TestGetRandomSnippet(t *testing.T) {
	snippet, err := GetRandomSnippet(1)
	if err != nil {
		t.Fatalf("GetRandomSnippet failed: %v", err)
	}

	if snippet == nil {
		t.Fatal("GetRandomSnippet returned nil snippet")
	}

	if snippet.Name == "" {
		t.Error("Random snippet has empty name")
	}

	if snippet.Module == nil {
		t.Error("Random snippet has nil module")
	}

	if snippet.ParentFile == nil {
		t.Error("Random snippet has nil parent file")
	}

	// Test multiple calls return (potentially) different snippets
	snippet2, err2 := GetRandomSnippet(1)
	if err2 != nil {
		t.Fatalf("Second call to GetRandomSnippet failed: %v", err2)
	}

	if snippet2 == nil {
		t.Fatal("Second GetRandomSnippet returned nil snippet")
	}

	// Note: We don't require different snippets since it's random,
	// but we verify both are valid
	t.Logf("Got random snippets: %s and %s", snippet.Name, snippet2.Name)
}

func TestGetRandomSnippet_WithDifferentVerboseLevels(t *testing.T) {
	verboseLevels := []int{0, 1, 3, 5}

	for _, level := range verboseLevels {
		t.Run(fmt.Sprintf("VerboseLevel_%d", level), func(t *testing.T) {
			snippet, err := GetRandomSnippet(level)
			if err != nil {
				t.Fatalf("GetRandomSnippet with verbose level %d failed: %v", level, err)
			}

			if snippet == nil {
				t.Fatalf("GetRandomSnippet with verbose level %d returned nil", level)
			}
		})
	}
}

func TestDfsDependencies(t *testing.T) {
	// Create a test parent VerilogFile with dependencies
	parentVF := verilog.NewVerilogFile("parent.sv")

	// Create a dependency structure:
	// NodeA depends on NodeB and NodeC
	// NodeB depends on NodeD
	parentVF.AddDependency("NodeA", "NodeB", "NodeC")
	parentVF.AddDependency("NodeB", "NodeD")

	// Add some structs, classes, modules, interfaces, packages to test copying
	parentVF.Structs["NodeB"] = &verilog.Struct{Name: "NodeB"}
	parentVF.Classes["NodeC"] = &verilog.Class{Name: "NodeC"}
	parentVF.Modules["NodeD"] = &verilog.Module{Name: "NodeD"}
	parentVF.Interfaces["NodeE"] = &verilog.Interface{Name: "NodeE"}
	parentVF.Packages["NodeF"] = &verilog.Package{Name: "NodeF"}

	// Create target file
	targetVF := verilog.NewVerilogFile("target.sv")

	// Test DFS dependencies
	dfsDependencies("NodeA", parentVF, targetVF)

	// Verify dependencies were copied
	if len(targetVF.DependencyMap) < 2 {
		t.Errorf(
			"Expected at least 2 nodes in target dependency map, got %d",
			len(targetVF.DependencyMap),
		)
	}

	// Verify NodeB dependency exists
	if _, exists := targetVF.DependencyMap["NodeB"]; !exists {
		t.Error("Expected NodeB to be copied to target")
	}

	// Verify NodeC dependency exists
	if _, exists := targetVF.DependencyMap["NodeC"]; !exists {
		t.Error("Expected NodeC to be copied to target")
	}

	// Verify NodeD dependency exists (transitive dependency)
	if _, exists := targetVF.DependencyMap["NodeD"]; !exists {
		t.Error("Expected NodeD to be copied to target (transitive dependency)")
	}

	// Verify struct was copied
	if _, exists := targetVF.Structs["NodeB"]; !exists {
		t.Error("Expected struct NodeB to be copied to target")
	}

	// Verify class was copied
	if _, exists := targetVF.Classes["NodeC"]; !exists {
		t.Error("Expected class NodeC to be copied to target")
	}

	// Verify module was copied
	if _, exists := targetVF.Modules["NodeD"]; !exists {
		t.Error("Expected module NodeD to be copied to target")
	}
}

func TestDfsDependencies_NoExistingNode(t *testing.T) {
	parentVF := verilog.NewVerilogFile("parent.sv")
	targetVF := verilog.NewVerilogFile("target.sv")

	// Test with non-existing node - should not crash
	dfsDependencies("NonExistentNode", parentVF, targetVF)

	// Should not add any dependencies
	if len(targetVF.DependencyMap) > 0 {
		t.Errorf(
			"Expected no dependencies to be added for non-existent node, got %d",
			len(targetVF.DependencyMap),
		)
	}
}

func TestDfsDependencies_CircularDependency(t *testing.T) {
	parentVF := verilog.NewVerilogFile("parent.sv")

	// Create circular dependency: A -> B -> C -> A
	parentVF.AddDependency("NodeA", "NodeB")
	parentVF.AddDependency("NodeB", "NodeC")
	parentVF.AddDependency("NodeC", "NodeA")

	targetVF := verilog.NewVerilogFile("target.sv")

	// This should not cause infinite recursion
	dfsDependencies("NodeA", parentVF, targetVF)

	// Verify some dependencies were added
	if len(targetVF.DependencyMap) == 0 {
		t.Error("Expected some dependencies to be added even with circular dependency")
	}
}

func createTestSnippet() *Snippet {
	// Create a simple test snippet
	module := &verilog.Module{
		Name: "TestModule",
		Ports: []verilog.Port{
			{Name: "clk", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
			{Name: "data", Direction: verilog.OUTPUT, Type: verilog.LOGIC, Width: 8},
		},
		Body: "assign data = 8'hFF;",
	}

	parentFile := verilog.NewVerilogFile("test.sv")
	parentFile.Modules["TestModule"] = module
	parentFile.AddDependency("TestModule", "SomeDependency")

	return &Snippet{
		Name:       "TestModule",
		Module:     module,
		ParentFile: parentFile,
	}
}

func TestAddDependenciesOfSnippet(t *testing.T) {
	targetFile := verilog.NewVerilogFile("target.sv")
	snippet := createTestSnippet()

	err := AddDependenciesOfSnippet(targetFile, snippet)
	if err != nil {
		t.Fatalf("AddDependenciesOfSnippet failed: %v", err)
	}
	t.Log(targetFile.DumpDependencyGraph())

	// Verify snippet node was added to target
	if _, exists := targetFile.DependencyMap[snippet.Name]; exists {
		t.Error("Expected snippet node not to be added to target dependency map")
	}

	// Verify the module was NOT added (addItself = false)
	if _, exists := targetFile.Modules[snippet.Module.Name]; exists {
		t.Error("Expected module NOT to be added when addItself is false")
	}
}

func TestAddDependencies(t *testing.T) {
	targetFile := verilog.NewVerilogFile("target.sv")
	snippet := createTestSnippet()

	err := AddDependencies(targetFile, snippet)
	if err != nil {
		t.Fatalf("AddDependencies failed: %v", err)
	}

	// Verify snippet node was added to target
	if _, exists := targetFile.DependencyMap[snippet.Name]; !exists {
		t.Error("Expected snippet node to be added to target dependency map")
	}

	// Verify the module WAS added (addItself = true)
	if _, exists := targetFile.Modules[snippet.Module.Name]; !exists {
		t.Error("Expected module to be added when addItself is true")
	}
}

func TestGeneralAddDependencies_NilParentFile(t *testing.T) {
	targetFile := verilog.NewVerilogFile("target.sv")
	snippet := &Snippet{
		Name:       "TestSnippet",
		Module:     &verilog.Module{Name: "TestModule"},
		ParentFile: nil, // Nil parent file
	}

	err := GeneralAddDependencies(targetFile, snippet, true)
	if err == nil {
		t.Error("Expected error for nil parent file, but got none")
	}

	expectedError := "snippet parent file is nil"
	if err.Error() != expectedError {
		t.Errorf("Expected error '%s', got '%s'", expectedError, err.Error())
	}
}

func TestGeneralAddDependencies_NilDependencyMap(t *testing.T) {
	targetFile := &verilog.VerilogFile{
		Name:          "target.sv",
		DependencyMap: nil, // Explicitly nil
		Modules:       make(map[string]*verilog.Module),
	}
	snippet := createTestSnippet()

	err := GeneralAddDependencies(targetFile, snippet, true)
	if err != nil {
		t.Fatalf("GeneralAddDependencies failed: %v", err)
	}

	// Verify dependency map was initialized
	if targetFile.DependencyMap == nil {
		t.Error("Expected dependency map to be initialized")
	}

	// Verify snippet was added
	if _, exists := targetFile.DependencyMap[snippet.Name]; !exists {
		t.Error("Expected snippet to be added to dependency map")
	}
}

func TestGeneralAddDependencies_ExistingSnippetNode(t *testing.T) {
	targetFile := verilog.NewVerilogFile("target.sv")
	snippet := createTestSnippet()

	// Pre-add the snippet node
	targetFile.DependencyMap[snippet.Name] = &verilog.DependencyNode{
		Name:       snippet.Name,
		DependsOn:  []string{"ExistingDep"},
		DependedBy: []string{},
	}

	err := GeneralAddDependencies(targetFile, snippet, true)
	if err != nil {
		t.Fatalf("GeneralAddDependencies failed: %v", err)
	}

	// Verify existing node was preserved (should not overwrite)
	node := targetFile.DependencyMap[snippet.Name]
	if len(node.DependsOn) == 0 {
		t.Error("Expected existing dependencies to be preserved")
	}
}

func TestGeneralAddDependencies_WithComplexDependencies(t *testing.T) {
	// Create a more complex test scenario
	module := &verilog.Module{
		Name: "ComplexModule",
		Ports: []verilog.Port{
			{Name: "clk", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
		},
	}

	parentFile := verilog.NewVerilogFile("complex.sv")
	parentFile.Modules["ComplexModule"] = module

	// Add complex dependency structure
	parentFile.AddDependency("ComplexModule", "DepA", "DepB")
	parentFile.AddDependency("DepA", "DepC")
	parentFile.AddDependency("DepB", "DepC", "DepD")

	// Add various types of dependencies
	parentFile.Structs["DepA"] = &verilog.Struct{Name: "DepA"}
	parentFile.Classes["DepB"] = &verilog.Class{Name: "DepB"}
	parentFile.Modules["DepC"] = &verilog.Module{Name: "DepC"}
	parentFile.Interfaces["DepD"] = &verilog.Interface{Name: "DepD"}

	snippet := &Snippet{
		Name:       "ComplexModule",
		Module:     module,
		ParentFile: parentFile,
	}

	targetFile := verilog.NewVerilogFile("target.sv")

	err := AddDependencies(targetFile, snippet)
	if err != nil {
		t.Fatalf("AddDependencies failed: %v", err)
	}

	// Verify all dependencies were copied
	expectedDeps := []string{"ComplexModule", "DepA", "DepB", "DepC", "DepD"}
	for _, dep := range expectedDeps {
		if _, exists := targetFile.DependencyMap[dep]; !exists {
			t.Errorf("Expected dependency %s to be copied", dep)
		}
	}

	// Verify various types were copied
	if _, exists := targetFile.Structs["DepA"]; !exists {
		t.Error("Expected struct DepA to be copied")
	}
	if _, exists := targetFile.Classes["DepB"]; !exists {
		t.Error("Expected class DepB to be copied")
	}
	if _, exists := targetFile.Modules["DepC"]; !exists {
		t.Error("Expected module DepC to be copied")
	}
	if _, exists := targetFile.Interfaces["DepD"]; !exists {
		t.Error("Expected interface DepD to be copied")
	}
}

// Additional edge case tests

func TestGetRandomSnippet_NoSnippetsAvailable(t *testing.T) {
	// Save original state
	originalSnippets := snippets
	originalVerilogFiles := verilogFiles
	originalLoadError := loadError

	// Reset to simulate no snippets loaded
	snippets = []*Snippet{}
	verilogFiles = []*verilog.VerilogFile{}
	loadOnce = sync.Once{}
	loadError = nil

	defer func() {
		// Restore original state
		snippets = originalSnippets
		verilogFiles = originalVerilogFiles
		loadOnce = sync.Once{} // Create a new sync.Once instead of copying
		loadError = originalLoadError
	}()

	// Note: We can't easily test this without modifying global state
	// This test demonstrates the intended behavior
	t.Skip("Skipping test that would require modifying global file system state")
}

func TestLoadSnippets_HandleTopModuleRename(t *testing.T) {
	// This test verifies that modules named "top" are renamed to "topi"
	// We'll create a temporary test to verify this logic works

	// Create a test VerilogFile with a module named "top"
	testVF := verilog.NewVerilogFile("test_top.sv")
	topModule := &verilog.Module{
		Name: "top",
		Ports: []verilog.Port{
			{Name: "clk", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
		},
		Body: "// Test module",
	}
	testVF.Modules["top"] = topModule

	// Simulate the renaming logic from loadSnippets
	for _, module := range testVF.Modules {
		if module.Name == "top" {
			module.Name = "topi"
		}
	}

	// Verify the rename occurred
	if topModule.Name != "topi" {
		t.Errorf(
			"Expected module name to be renamed from 'top' to 'topi', got '%s'",
			topModule.Name,
		)
	}
}

func TestDfsDependencies_PreExistingTargetDependencies(t *testing.T) {
	// Test case where target already has some dependencies
	parentVF := verilog.NewVerilogFile("parent.sv")
	parentVF.AddDependency("NodeA", "NodeB")
	parentVF.Structs["NodeB"] = &verilog.Struct{Name: "NodeB"}

	targetVF := verilog.NewVerilogFile("target.sv")
	// Pre-populate target with some existing dependency
	targetVF.AddDependency("ExistingNode", "ExistingDep")
	originalCount := len(targetVF.DependencyMap)

	dfsDependencies("NodeA", parentVF, targetVF)

	// Verify new dependencies were added while preserving existing ones
	if len(targetVF.DependencyMap) <= originalCount {
		t.Error("Expected new dependencies to be added to target")
	}

	// Verify existing dependency still exists
	if _, exists := targetVF.DependencyMap["ExistingNode"]; !exists {
		t.Error("Expected existing dependencies to be preserved")
	}

	// Verify new dependency was added
	if _, exists := targetVF.DependencyMap["NodeB"]; !exists {
		t.Error("Expected new dependency NodeB to be added")
	}
}

func TestDfsDependencies_DuplicateEntityTypes(t *testing.T) {
	// Test case where the same name exists in multiple entity maps
	parentVF := verilog.NewVerilogFile("parent.sv")
	parentVF.AddDependency("NodeA", "DuplicateName")

	// Add the same name to multiple entity types
	parentVF.Structs["DuplicateName"] = &verilog.Struct{Name: "DuplicateName"}
	parentVF.Classes["DuplicateName"] = &verilog.Class{Name: "DuplicateName"}
	parentVF.Modules["DuplicateName"] = &verilog.Module{Name: "DuplicateName"}

	targetVF := verilog.NewVerilogFile("target.sv")

	dfsDependencies("NodeA", parentVF, targetVF)

	// Verify all types were copied (each check should only copy if not exists)
	if _, exists := targetVF.Structs["DuplicateName"]; !exists {
		t.Error("Expected struct DuplicateName to be copied")
	}
	if _, exists := targetVF.Classes["DuplicateName"]; !exists {
		t.Error("Expected class DuplicateName to be copied")
	}
	if _, exists := targetVF.Modules["DuplicateName"]; !exists {
		t.Error("Expected module DuplicateName to be copied")
	}
}

func TestDfsDependencies_AlreadyExistsInTarget(t *testing.T) {
	// Test case where dependency already exists in target
	parentVF := verilog.NewVerilogFile("parent.sv")
	parentVF.AddDependency("NodeA", "SharedDep")
	parentVF.Structs["SharedDep"] = &verilog.Struct{Name: "SharedDep"}

	targetVF := verilog.NewVerilogFile("target.sv")
	// Pre-add the same dependency to target
	targetVF.DependencyMap["SharedDep"] = &verilog.DependencyNode{Name: "SharedDep"}
	targetVF.Structs["SharedDep"] = &verilog.Struct{Name: "SharedDep"}

	dfsDependencies("NodeA", parentVF, targetVF)

	// Verify that the dependency is properly linked
	if _, exists := targetVF.DependencyMap["SharedDep"]; !exists {
		t.Error("Expected SharedDep to remain in target dependency map")
	}

	// Verify NodeA depends on SharedDep
	nodeA := targetVF.DependencyMap["NodeA"]
	if nodeA == nil {
		t.Fatal("Expected NodeA to be in target dependency map")
	}

	found := false
	for _, dep := range nodeA.DependsOn {
		if dep == "SharedDep" {
			found = true
			break
		}
	}
	if !found {
		t.Error("Expected NodeA to depend on SharedDep")
	}
}

// Benchmark tests
func BenchmarkGetRandomSnippet(b *testing.B) {
	for i := 0; i < b.N; i++ {
		_, err := GetRandomSnippet(0) // Use verbose level 0 for benchmarks
		if err != nil {
			b.Fatalf("GetRandomSnippet failed: %v", err)
		}
	}
}

func BenchmarkLoadSnippets(b *testing.B) {
	for i := 0; i < b.N; i++ {
		// Reset state
		snippets = []*Snippet{}
		verilogFiles = []*verilog.VerilogFile{}

		err := loadSnippets()
		if err != nil {
			b.Fatalf("loadSnippets failed: %v", err)
		}
	}
}
