package snippets

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

func TestWriteFileAsSnippets(t *testing.T) {
	t.Skip("Skipping test as not ran manually")
	rootDir, err := utils.GetRootDir()
	if err != nil {
		t.Fatalf("failed to get root directory: %v", err)
	}
	svFilePath := filepath.Join(rootDir, "snippets", "slang", "AllTypes.sv")
	content, err := utils.ReadFileContent(svFilePath)
	if err != nil {
		t.Fatalf("failed to read file content: %v", err)
	}
	svFile, err := verilog.ParseVerilog(content, 5)
	if err != nil {
		t.Fatalf("failed to parse Verilog file: %v", err)
	}
	err = WriteFileAsSnippets(svFile)
	if err != nil {
		t.Fatalf("failed to write file as snippets: %v", err)
	}
}

func TestSplitInterfaceDependencies(t *testing.T) {
	// Get the root directory to construct the path to test files
	rootDir, err := utils.GetRootDir()
	if err != nil {
		t.Fatalf("Failed to get root directory: %v", err)
	}

	// Parse the interface module test file
	testFilePath := filepath.Join(rootDir, "testfiles", "sv", "ok", "interface_module.sv")
	fileContent, err := os.ReadFile(testFilePath)
	if err != nil {
		t.Fatalf("Failed to read interface_module.sv: %v", err)
	}

	svFile, err := verilog.ParseVerilog(string(fileContent), 0)
	if err != nil {
		t.Fatalf("Failed to parse interface_module.sv: %v", err)
	}

	// Set the file name manually since ParseVerilog doesn't set it
	svFile.Name = testFilePath

	// Verify initial structure
	if len(svFile.Interfaces) != 1 {
		t.Fatalf("Expected 1 interface, got %d", len(svFile.Interfaces))
	}

	if len(svFile.Modules) != 1 {
		t.Fatalf("Expected 1 module, got %d", len(svFile.Modules))
	}

	// Get the target module
	var targetModule *verilog.Module
	for _, module := range svFile.Modules {
		if module.Name == "interface_module" {
			targetModule = module
			break
		}
	}

	if targetModule == nil {
		t.Fatalf("Could not find interface_module")
	}

	// Verify the module has interface ports
	interfacePortCount := 0
	for _, port := range targetModule.Ports {
		if port.IsInterfacePort() {
			interfacePortCount++
		}
	}

	if interfacePortCount != 2 {
		t.Errorf("Expected 2 interface ports, got %d", interfacePortCount)
	}

	// Create a snippet from the module
	snippet := &Snippet{
		Name:       targetModule.Name,
		Module:     targetModule,
		ParentFile: svFile,
	}

	// Create a new VerilogFile for the snippet
	snippetFile := verilog.NewVerilogFile(targetModule.Name + ".sv")

	// Test AddDependencies function
	err = AddDependencies(snippetFile, snippet)
	if err != nil {
		t.Fatalf("Failed to add dependencies: %v", err)
	}

	// Verify the interface was added to the dependency map
	if _, exists := snippetFile.DependencyMap["simple_bus"]; !exists {
		t.Error("Expected simple_bus interface to be in dependency map")
	}

	// Verify the interface was copied to the snippet file
	if _, exists := snippetFile.Interfaces["simple_bus"]; !exists {
		t.Error("Expected simple_bus interface to be copied to snippet file")
	}

	// Verify the module was added
	if _, exists := snippetFile.Modules["interface_module"]; !exists {
		t.Error("Expected interface_module to be in snippet file")
	}

	// Generate the content and verify it includes the interface
	content, err := verilog.PrintVerilogFile(snippetFile)
	if err != nil {
		t.Fatalf("Failed to print VerilogFile: %v", err)
	}

	// Debug: Print the actual output for inspection
	t.Logf("Generated snippet content:\n%s", content)

	// Verify the content includes the interface definition
	if !strings.Contains(content, "interface simple_bus") {
		t.Error("Expected snippet content to include 'interface simple_bus'")
	}

	// Verify the content includes modport definitions
	if !strings.Contains(content, "modport master") {
		t.Error("Expected snippet content to include 'modport master'")
	}

	if !strings.Contains(content, "modport slave") {
		t.Error("Expected snippet content to include 'modport slave'")
	}

	// Verify the content includes the module with interface ports
	if !strings.Contains(content, "simple_bus.slave in_bus") {
		t.Error("Expected snippet content to include 'simple_bus.slave in_bus'")
	}

	if !strings.Contains(content, "simple_bus.master out_bus") {
		t.Error("Expected snippet content to include 'simple_bus.master out_bus'")
	}

	// Test writing the snippet to file
	err = snippet.writeSnippetToFile()
	if err != nil {
		t.Logf("Warning: Failed to write snippet to file: %v", err)
	} else {
		// Only verify file contents if file writing succeeded
		outputPath := filepath.Join(rootDir, "isolated", "interface_module", "interface_module.sv")
		outputContent, err := os.ReadFile(outputPath)
		if err != nil {
			t.Logf("Warning: Failed to read output file %s: %v", outputPath, err)
		} else {
			outputStr := string(outputContent)
			if !strings.Contains(outputStr, "interface simple_bus") {
				t.Error("Expected output file to include 'interface simple_bus'")
			}

			if !strings.Contains(outputStr, "simple_bus.slave in_bus") {
				t.Error("Expected output file to include 'simple_bus.slave in_bus'")
			}
		}

		// Clean up the test output
		err = os.RemoveAll(filepath.Join(rootDir, "isolated", "interface_module"))
		if err != nil {
			t.Logf("Warning: Failed to clean up test output: %v", err)
		}
	}
}

// TestSnippetModuleDependencyResolution tests that module dependencies are properly included in generated snippets
func TestSnippetModuleDependencyResolution(t *testing.T) {
	testContent := `
module base_module (
  input logic [7:0] a,
  output logic [7:0] out
);
  assign out = a + 8'h01;
endmodule

module dependent_module (
  input logic [7:0] data_in,
  output logic [7:0] data_out
);
  base_module inst (
    .a(data_in),
    .out(data_out)
  );
endmodule
`

	// Parse the content
	svFile, err := verilog.ParseVerilog(testContent, 0)
	if err != nil {
		t.Fatalf("Failed to parse test content: %v", err)
	}

	// Verify dependency tracking works
	if deps, exists := svFile.DependencyMap["dependent_module"]; exists {
		found := false
		for _, dep := range deps.DependsOn {
			if dep == "base_module" {
				found = true
				break
			}
		}
		if !found {
			t.Error("Expected dependent_module to depend on base_module")
		}
	} else {
		t.Error("Expected dependent_module to be found in dependency map")
	}

	// Test snippet generation
	dependentModule := svFile.Modules["dependent_module"]
	if dependentModule == nil {
		t.Fatal("dependent_module not found")
	}

	snippet := &Snippet{
		Name:       dependentModule.Name,
		Module:     dependentModule,
		ParentFile: svFile,
	}

	// Create target file for snippet
	targetFile := verilog.NewVerilogFile("test_snippet.sv")

	// Add dependencies
	err = AddDependencies(targetFile, snippet)
	if err != nil {
		t.Fatalf("Failed to add dependencies: %v", err)
	}

	// Verify that base_module is included in the target file
	if _, exists := targetFile.Modules["base_module"]; !exists {
		t.Error("Expected base_module to be included in snippet dependencies")
	}

	// Verify that dependent_module is included
	if _, exists := targetFile.Modules["dependent_module"]; !exists {
		t.Error("Expected dependent_module to be included in snippet")
	}

	// Test that the generated content includes both modules
	content, err := verilog.PrintVerilogFile(targetFile)
	if err != nil {
		t.Fatalf("Failed to print Verilog file: %v", err)
	}

	if !strings.Contains(content, "module base_module") {
		t.Error("Expected generated content to contain base_module definition")
	}
	if !strings.Contains(content, "module dependent_module") {
		t.Error("Expected generated content to contain dependent_module definition")
	}
}
