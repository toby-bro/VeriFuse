package testgen

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

func TestGenerateInterfaceStimulus(t *testing.T) {
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

	// Verify that we parsed the interface correctly
	if len(svFile.Interfaces) != 1 {
		t.Fatalf("Expected 1 interface, got %d", len(svFile.Interfaces))
	}

	if len(svFile.Modules) != 1 {
		t.Fatalf("Expected 1 module, got %d", len(svFile.Modules))
	}

	// Get the interface and module
	var simpleInterface *verilog.Interface
	for _, intf := range svFile.Interfaces {
		if intf.Name == "simple_bus" {
			simpleInterface = intf
			break
		}
	}

	if simpleInterface == nil {
		t.Fatalf("Could not find simple_bus interface")
	}

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

	// Verify interface structure
	expectedVariables := []string{"data", "valid", "ready"}
	if len(simpleInterface.Variables) != len(expectedVariables) {
		t.Errorf(
			"Expected %d variables, got %d",
			len(expectedVariables),
			len(simpleInterface.Variables),
		)
	}

	for _, expectedVar := range expectedVariables {
		found := false
		for _, variable := range simpleInterface.Variables {
			if variable.Name == expectedVar {
				found = true
				break
			}
		}
		if !found {
			t.Errorf("Expected variable %s not found in interface", expectedVar)
		}
	}

	// Verify modports
	expectedModports := []string{"master", "slave"}
	if len(simpleInterface.ModPorts) != len(expectedModports) {
		t.Errorf(
			"Expected %d modports, got %d",
			len(expectedModports),
			len(simpleInterface.ModPorts),
		)
	}

	// Create generator and test interface stimulus generation
	gen := NewGenerator(targetModule, svFile.Name, svFile)

	// Test cases for interface stimulus generation
	testCases := []struct {
		portName            string
		interfaceType       string
		expectedContains    []string
		expectedNotContains []string
	}{
		{
			portName:      "in_bus",
			interfaceType: "simple_bus.slave",
			expectedContains: []string{
				"// Initialize interface in_bus (simple_bus.slave)",
				"in_bus.ready = 1'b1;",
			},
			expectedNotContains: []string{
				"in_bus.data",
				"in_bus.valid",
			},
		},
		{
			portName:      "out_bus",
			interfaceType: "simple_bus.master",
			expectedContains: []string{
				"// Initialize interface out_bus (simple_bus.master)",
				"out_bus.data = 8'h55;",
				"out_bus.valid = 1'b1;",
			},
			expectedNotContains: []string{
				"out_bus.ready",
			},
		},
	}

	for _, tc := range testCases {
		t.Run("Port_"+tc.portName, func(t *testing.T) {
			// Find the port
			var testPort *verilog.Port
			for _, port := range targetModule.Ports {
				if port.Name == tc.portName {
					testPort = &port
					break
				}
			}

			if testPort == nil {
				t.Fatalf("Could not find port %s", tc.portName)
			}

			// Verify it's an interface port
			if !testPort.IsInterfacePort() {
				t.Errorf("Port %s should be an interface port", tc.portName)
			}

			// Verify the interface type
			if testPort.GetInterfaceType() != tc.interfaceType {
				t.Errorf("Port %s interface type: expected %s, got %s",
					tc.portName, tc.interfaceType, testPort.GetInterfaceType())
			}

			// Generate stimulus
			stimulus := gen.GenerateInterfaceStimulus(*testPort)

			// Verify expected content is present
			for _, expected := range tc.expectedContains {
				if !strings.Contains(stimulus, expected) {
					t.Errorf(
						"Port %s stimulus missing expected content: %s\nGenerated stimulus:\n%s",
						tc.portName,
						expected,
						stimulus,
					)
				}
			}

			// Verify unwanted content is not present
			for _, notExpected := range tc.expectedNotContains {
				if strings.Contains(stimulus, notExpected) {
					t.Errorf(
						"Port %s stimulus contains unwanted content: %s\nGenerated stimulus:\n%s",
						tc.portName,
						notExpected,
						stimulus,
					)
				}
			}
		})
	}
}

func TestGenerateInterfaceStimulusWithMissingInterface(t *testing.T) {
	// Create a minimal module with an interface port but no interface definition
	module := &verilog.Module{
		Name: "test_module",
		Ports: []verilog.Port{
			{
				Name:          "test_if",
				InterfaceName: "missing_interface",
				ModportName:   "master",
			},
		},
	}

	// Create an empty VerilogFile
	svFile := &verilog.VerilogFile{
		Name:       "test.sv",
		Interfaces: make(map[string]*verilog.Interface),
	}

	gen := NewGenerator(module, svFile.Name, svFile)

	// Generate stimulus for the port with missing interface
	stimulus := gen.GenerateInterfaceStimulus(module.Ports[0])

	// Should generate a warning comment
	expectedWarning := "// Interface missing_interface not found, using safe defaults"
	if !strings.Contains(stimulus, expectedWarning) {
		t.Errorf("Expected warning comment not found in stimulus: %s\nGenerated stimulus:\n%s",
			expectedWarning, stimulus)
	}
}

func TestGenerateInterfaceStimulusWithMissingModport(t *testing.T) {
	// Create a test interface without the requested modport
	testInterface := &verilog.Interface{
		Name: "test_interface",
		Variables: []*verilog.Variable{
			{Name: "data", Type: verilog.LOGIC, Width: 8},
		},
		ModPorts: []verilog.ModPort{
			{
				Name: "slave",
				Signals: []verilog.ModPortSignal{
					{Name: "data", Direction: verilog.INPUT},
				},
			},
		},
	}

	module := &verilog.Module{
		Name: "test_module",
		Ports: []verilog.Port{
			{
				Name:          "test_if",
				InterfaceName: "test_interface",
				ModportName:   "master", // This modport doesn't exist
			},
		},
	}

	svFile := &verilog.VerilogFile{
		Name: "test.sv",
		Interfaces: map[string]*verilog.Interface{
			"test_interface": testInterface,
		},
	}

	gen := NewGenerator(module, svFile.Name, svFile)

	// Generate stimulus for the port with missing modport
	stimulus := gen.GenerateInterfaceStimulus(module.Ports[0])

	// Should generate a warning comment
	expectedWarning := "// Modport master not found, using common defaults"
	if !strings.Contains(stimulus, expectedWarning) {
		t.Errorf("Expected warning comment not found in stimulus: %s\nGenerated stimulus:\n%s",
			expectedWarning, stimulus)
	}
}

func TestModuleWithInterfaceDependencyPrinting(t *testing.T) {
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

	// Test 1: Verify dependency mapping includes interface
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

	// Test 2: Verify interface is in dependency map
	if _, exists := svFile.DependencyMap["simple_bus"]; !exists {
		t.Error("Expected simple_bus interface to be in dependency map")
	}

	// Test 3: Print the VerilogFile and verify interface is included
	output, err := verilog.PrintVerilogFile(svFile)
	if err != nil {
		t.Fatalf("Failed to print VerilogFile: %v", err)
	}

	// Debug: Print the actual output
	// t.Logf("PrintVerilogFile output:\n%s", output)

	// Verify that the interface definition is included in the output
	if !strings.Contains(output, "interface simple_bus") {
		t.Errorf(
			"Expected interface definition 'interface simple_bus' in output, but not found. Output:\n%s",
			output,
		)
	}

	// Verify that the interface comes before the module that uses it
	interfaceIndex := strings.Index(output, "interface simple_bus")
	moduleIndex := strings.Index(output, "module interface_module")

	if interfaceIndex == -1 {
		t.Error("Interface definition not found in output")
	}
	if moduleIndex == -1 {
		t.Error("Module definition not found in output")
	}
	if interfaceIndex > moduleIndex {
		t.Error("Interface should be defined before the module that uses it")
	}

	// Verify modport definitions are included
	if !strings.Contains(output, "modport master") {
		t.Error("Expected 'modport master' in interface definition")
	}
	if !strings.Contains(output, "modport slave") {
		t.Error("Expected 'modport slave' in interface definition")
	}

	// Verify interface variables are included
	if !strings.Contains(output, "logic [7:0] data") {
		t.Error("Expected interface variable 'logic [7:0] data' in output")
	}
	if !strings.Contains(output, "logic valid") {
		t.Error("Expected interface variable 'logic valid' in output")
	}
	if !strings.Contains(output, "logic ready") {
		t.Error("Expected interface variable 'logic ready' in output")
	}
}
