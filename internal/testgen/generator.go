package testgen

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

// Generator handles testbench generation
type Generator struct {
	module   *verilog.Module
	fileName string
}

// NewGenerator creates a new testbench generator
func NewGenerator(module *verilog.Module, fileName string) *Generator {
	// We don't need to extract enums here anymore since they're embedded in the mocked file
	return &Generator{
		module:   module,
		fileName: fileName,
	}
}

// GenerateTestbenchesInDir creates both SystemVerilog and C++ testbenches in the specified directory
func (g *Generator) GenerateTestbenchesInDir(outputDir string) error {
	// Ensure the output directory exists
	if err := os.MkdirAll(outputDir, 0o755); err != nil {
		return fmt.Errorf("failed to create output directory %s: %w", outputDir, err)
	}

	if err := g.GenerateSVTestbench(outputDir); err != nil {
		return fmt.Errorf("failed to generate SystemVerilog testbench in %s: %v", outputDir, err)
	}
	return nil
}

// generateSVPortDeclarations generates the logic declarations for testbench ports
func (g *Generator) generateSVPortDeclarations() string {
	var declarations strings.Builder
	for _, port := range g.module.Ports {
		typeDecl := verilog.LOGIC.String() + " "
		if port.Width > 1 {
			typeDecl += fmt.Sprintf(" [%d:0] ", port.Width-1)
		}
		portName := strings.TrimSpace(port.Name)
		declarations.WriteString(fmt.Sprintf("    %s%s;\n", typeDecl, portName))
	}
	return declarations.String()
}

// generateSVModuleInstantiation generates the DUT instantiation string
func (g *Generator) generateSVModuleInstantiation() string {
	var moduleInst strings.Builder
	moduleInst.WriteString("    " + g.module.Name)
	// Add parameters if present
	if len(g.module.Parameters) > 0 {
		moduleInst.WriteString(" #(\n")

		// Track valid parameters to include (skip qualifiers)
		paramCount := 0

		for _, param := range g.module.Parameters {
			// Skip parameters without a name or type qualifiers incorrectly parsed as parameters
			if param.Name == "" || param.Name == "unsigned" || param.Name == "signed" {
				continue
			}

			// Add comma between parameters
			if paramCount > 0 {
				moduleInst.WriteString(",\n")
			}
			paramCount++

			defaultVal := param.DefaultValue
			if defaultVal == "" {
				switch param.Type { //nolint:exhaustive
				case verilog.INT:
					defaultVal = "1"
				case verilog.BIT:
					defaultVal = "1'b0"
				case verilog.LOGIC:
					defaultVal = "1'b0"
				case verilog.REAL:
					defaultVal = "0.0"
				case verilog.STRING:
					defaultVal = "\"\""
				case verilog.TIME:
					defaultVal = "0"
				case verilog.INTEGER:
					defaultVal = "0"
				case verilog.REG:
					defaultVal = "1'b0"
				case verilog.WIRE:
					defaultVal = "1'b0"
				case verilog.REALTIME:
					defaultVal = "0.0"
				case verilog.BYTE:
					defaultVal = "8'h00"
				case verilog.SHORTINT:
					defaultVal = "0"
				case verilog.LONGINT:
					defaultVal = "0"
				case verilog.SHORTREAL:
					defaultVal = "0.0"
				default:
					defaultVal = ""
				}
			}

			moduleInst.WriteString(fmt.Sprintf("        .%s(%s)", param.Name, defaultVal))
		}

		moduleInst.WriteString("\n    )")
	}

	moduleInst.WriteString(" dut (\n")

	// Add explicit port connections
	for i, port := range g.module.Ports {
		portName := strings.TrimSpace(port.Name)
		moduleInst.WriteString(fmt.Sprintf("        .%s(%s)", portName, portName))
		if i < len(g.module.Ports)-1 {
			moduleInst.WriteString(",\n")
		}
	}

	moduleInst.WriteString("\n    );\n")
	return moduleInst.String()
}

// identifyClockAndResetPorts scans ports to find clock and reset signals
func (g *Generator) identifyClockAndResetPorts() (clockPorts []string, resetPort string, isActiveHigh bool) {
	for _, port := range g.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			portName := strings.TrimSpace(port.Name)
			portNameLower := strings.ToLower(portName)

			// Identify clock ports by name convention
			if strings.Contains(portNameLower, "clk") || strings.Contains(portNameLower, "clock") {
				clockPorts = append(clockPorts, portName)
				continue // A port can't be both clock and reset for this logic
			}

			// Identify reset ports by name convention
			if resetPort == "" &&
				(strings.Contains(portNameLower, "rst") || strings.Contains(portNameLower, "reset")) {
				resetPort = portName
				// Determine if active high or low (active low has _n, _ni, or _l suffix)
				isActiveHigh = !strings.HasSuffix(portNameLower, "_n") &&
					!strings.HasSuffix(portNameLower, "_ni") &&
					!strings.HasSuffix(portNameLower, "_l")
			}
		}
	}
	return clockPorts, resetPort, isActiveHigh
}

// generateSVInputReads generates code to read input values from files
func (g *Generator) generateSVInputReads(clockPorts []string, resetPort string) (string, int) {
	var inputReads strings.Builder
	var inputCount int

	for _, port := range g.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			portName := strings.TrimSpace(port.Name)

			// Skip clock and reset ports, handled separately
			isClockPort := false
			for _, clockPort := range clockPorts {
				if portName == clockPort {
					isClockPort = true
					break
				}
			}
			if isClockPort || portName == resetPort {
				// Initialize clocks and reset to 0 (or appropriate initial state if needed later)
				inputReads.WriteString(fmt.Sprintf("        %s = 0;\n", portName))
				continue
			}

			inputCount++
			fileName := fmt.Sprintf("input_%s.hex", portName)

			inputReads.WriteString(fmt.Sprintf(`
        fd = $fopen("%s", "r");
        if (fd == 0) begin
            $display("Error: Unable to open %s");
            $finish;
        end
        status = $fgets(line, fd);
        `, fileName, fileName))

			if port.Width > 1 {
				inputReads.WriteString(
					fmt.Sprintf("status = $sscanf(line, \"%%h\", %s);\n", portName),
				)
			} else {
				inputReads.WriteString(fmt.Sprintf("status = $sscanf(line, \"%%b\", %s);\n", portName))
			}

			inputReads.WriteString("        $fclose(fd);\n")
		}
	}
	return inputReads.String(), inputCount
}

// generateSVResetToggling generates code to toggle the reset signal
func (g *Generator) generateSVResetToggling(resetPort string, isActiveHigh bool) string {
	if resetPort == "" {
		return "" // No reset port found
	}

	var resetToggle strings.Builder
	resetToggle.WriteString(fmt.Sprintf("\n        // Toggle reset signal %s\n", resetPort))
	if isActiveHigh {
		resetToggle.WriteString(
			fmt.Sprintf("        %s = 1; // Assert reset (active high)\n", resetPort),
		)
		resetToggle.WriteString("        #10;\n")
		resetToggle.WriteString(fmt.Sprintf("        %s = 0; // De-assert reset\n", resetPort))
	} else {
		resetToggle.WriteString(fmt.Sprintf("        %s = 0; // Assert reset (active low)\n", resetPort))
		resetToggle.WriteString("        #10;\n")
		resetToggle.WriteString(fmt.Sprintf("        %s = 1; // De-assert reset\n", resetPort))
	}
	resetToggle.WriteString("        #10; // Wait after de-asserting reset\n")
	return resetToggle.String()
}

// generateSVClockToggling generates code to toggle clock signals
func (g *Generator) generateSVClockToggling(clockPorts []string) string {
	if len(clockPorts) == 0 {
		// If no clock ports, just add a delay
		return "\n        // Allow module to process\n        #10;\n"
	}

	var clockToggle strings.Builder
	clockToggle.WriteString("\n        // Toggle clocks for several cycles\n")
	clockToggle.WriteString("        repeat (10) begin\n")

	for _, clockPort := range clockPorts {
		clockToggle.WriteString(fmt.Sprintf("            %s = 0;\n", clockPort))
	}
	clockToggle.WriteString("            #5;\n")

	for _, clockPort := range clockPorts {
		clockToggle.WriteString(fmt.Sprintf("            %s = 1;\n", clockPort))
	}
	clockToggle.WriteString("            #5;\n")

	clockToggle.WriteString("        end\n")
	return clockToggle.String()
}

// generateSVOutputWrites generates code to write output values to files
func (g *Generator) generateSVOutputWrites() (string, int) {
	var outputWrites strings.Builder
	var outputCount int

	for _, port := range g.module.Ports {
		if port.Direction == verilog.OUTPUT {
			outputCount++
			portName := strings.TrimSpace(port.Name)
			fileName := fmt.Sprintf("output_%s.hex", portName)

			outputWrites.WriteString(fmt.Sprintf(`
        fd = $fopen("%s", "w");
        `, fileName))

			if port.Width > 1 {
				outputWrites.WriteString(fmt.Sprintf("$fwrite(fd, \"%%h\", %s);\n", portName))
			} else {
				outputWrites.WriteString(fmt.Sprintf("$fwrite(fd, \"%%0b\", %s);\n", portName))
			}

			outputWrites.WriteString("        $fclose(fd);\n")
		}
	}
	return outputWrites.String(), outputCount
}

// GenerateSVTestbench creates the SystemVerilog testbench in the specified directory
func (g *Generator) GenerateSVTestbench(outputDir string) error {
	// Generate different parts of the testbench
	declarations := g.generateSVPortDeclarations()
	moduleInst := g.generateSVModuleInstantiation()
	clockPorts, resetPort, isActiveHigh := g.identifyClockAndResetPorts()
	inputReadsStr, inputCount := g.generateSVInputReads(clockPorts, resetPort)
	resetToggleStr := g.generateSVResetToggling(resetPort, isActiveHigh)
	clockToggleStr := g.generateSVClockToggling(clockPorts)
	outputWritesStr, outputCount := g.generateSVOutputWrites()

	// Include the mocked module file - assumes the verilog file is in the same dir
	// The path might need adjustment depending on where the worker copies the verilog file relative to testbench.sv
	// Assuming they are in the same directory (outputDir) for now.
	includeDirective := fmt.Sprintf("`include \"../%s\"", g.fileName)

	// Apply the generated code to the template
	testbench := fmt.Sprintf(svTestbenchTemplate,
		includeDirective,
		declarations,
		moduleInst,
		inputCount,
		inputReadsStr,
		resetToggleStr, // Apply reset before clock toggling
		clockToggleStr, // Apply clock toggling after reset
		outputCount,
		outputWritesStr)

	// Write to the specified output directory
	svTestbenchPath := filepath.Join(outputDir, "testbench.sv")
	return utils.WriteFileContent(svTestbenchPath, testbench)
}

// getCXXRTLPortType returns a string representation of the C++ type for CXXRTL port access.
func getCXXRTLPortType(width int) string {
	if width == 1 {
		return "bool"
	}
	// For multi-bit ports, CXXRTL's set/get are templated.
	// Standard integer types are suitable.
	if width <= 8 {
		return "uint8_t"
	} else if width <= 16 {
		return "uint16_t"
	} else if width <= 32 {
		return "uint32_t"
	}
	return "uint64_t" // Default for wider ports
}

func (g *Generator) generateCXXRTLInputDeclarations() string {
	var inputDecls strings.Builder
	for _, port := range g.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			portName := strings.TrimSpace(port.Name)
			// cppType := getCXXRTLPortType(port.Width) // Not directly needed for declaration type
			varDeclType := getCXXRTLPortType(port.Width)
			if port.Width > 1 && port.Width <= 64 && port.Width != 8 && port.Width != 16 &&
				port.Width != 32 &&
				port.Width != 64 {
				varDeclType = fmt.Sprintf("uint%d_t", nextPowerOfTwo(port.Width))
			}
			inputDecls.WriteString(fmt.Sprintf("    %s %s;\n", varDeclType, portName))
		}
	}
	return inputDecls.String()
}

func (g *Generator) generateCXXRTLInputReads(outputDir string) string {
	var inputReads strings.Builder
	for _, port := range g.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			portName := strings.TrimSpace(port.Name)
			fileName := fmt.Sprintf("input_%s.hex", portName)

			inputReads.WriteString(fmt.Sprintf(`    std::ifstream %s_file("%s/%s");
    if (!%s_file.is_open()) {
        std::cerr << "Error opening file: %s" << std::endl;
        return 1;
    }
`, portName, outputDir, fileName, portName, fileName))

			if port.Width > 1 {
				inputReads.WriteString(fmt.Sprintf("    %s_file >> std::hex >> %s;\n",
					portName, portName))
			} else {
				inputReads.WriteString(fmt.Sprintf(`    char %s_char_val;
    %s_file >> %s_char_val;
    %s = (%s_char_val == '1'); // Assign bool directly
`, portName, portName, portName, portName, portName))
			}
			inputReads.WriteString(fmt.Sprintf("    %s_file.close();\n", portName))
		}
	}
	return inputReads.String()
}

func (g *Generator) generateCXXRTLInputApply(instanceName string) string {
	var inputApply strings.Builder
	for _, port := range g.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			portName := strings.TrimSpace(port.Name)
			cppType := getCXXRTLPortType(port.Width)
			inputApply.WriteString(
				fmt.Sprintf(
					"    %s.p_%s.set<%s>(%s);\n",
					instanceName,
					portName,
					cppType,
					portName,
				),
			)
		}
	}
	inputApply.WriteString(
		fmt.Sprintf("    %s.step(); // Initial step after applying all inputs\n", instanceName),
	)
	return inputApply.String()
}

func (g *Generator) generateCXXRTLResetLogic(
	instanceName string,
	resetPortName string,
	isActiveHigh bool,
) string {
	if resetPortName == "" {
		return ""
	}
	var resetLogic strings.Builder
	resetLogic.WriteString(fmt.Sprintf("\n    // Toggle reset signal p_%s\n", resetPortName))
	resetSignalType := getCXXRTLPortType(1) // Reset is typically single bit
	if isActiveHigh {
		resetLogic.WriteString(
			fmt.Sprintf(
				"    %s.p_%s.set<%s>(true); // Assert reset (active high)\n",
				instanceName,
				resetPortName,
				resetSignalType,
			),
		)
	} else {
		resetLogic.WriteString(fmt.Sprintf("    %s.p_%s.set<%s>(false); // Assert reset (active low)\n", instanceName, resetPortName, resetSignalType))
	}
	resetLogic.WriteString(
		fmt.Sprintf("    %s.step(); // Step to propagate reset assertion\n", instanceName),
	)

	if isActiveHigh {
		resetLogic.WriteString(
			fmt.Sprintf(
				"    %s.p_%s.set<%s>(false); // De-assert reset\n",
				instanceName,
				resetPortName,
				resetSignalType,
			),
		)
	} else {
		resetLogic.WriteString(fmt.Sprintf("    %s.p_%s.set<%s>(true); // De-assert reset\n", instanceName, resetPortName, resetSignalType))
	}
	resetLogic.WriteString(
		fmt.Sprintf("    %s.step(); // Step to propagate reset de-assertion\n", instanceName),
	)
	resetLogic.WriteString(
		fmt.Sprintf("    %s.step(); // Extra step for settling after reset\n", instanceName),
	)
	return resetLogic.String()
}

func (g *Generator) generateCXXRTLClockLogic(instanceName string, clockPortNames []string) string {
	if len(clockPortNames) == 0 {
		var noClockLogic strings.Builder
		noClockLogic.WriteString(
			fmt.Sprintf(
				"\n    // No clock found, performing a few steps for combinational logic to settle\n",
			),
		)
		noClockLogic.WriteString(fmt.Sprintf("    %s.step();\n", instanceName))
		noClockLogic.WriteString(fmt.Sprintf("    %s.step();\n", instanceName))
		return noClockLogic.String()
	}

	var clockLogic strings.Builder
	clockLogic.WriteString("\n    // Clock toggling\n")
	clockSignalType := getCXXRTLPortType(1) // Clock is typically single bit
	clockLogic.WriteString("    for (int cycle = 0; cycle < 10; cycle++) {\n")
	for _, clockPort := range clockPortNames {
		clockLogic.WriteString(
			fmt.Sprintf(
				"        %s.p_%s.set<%s>(false);\n",
				instanceName,
				clockPort,
				clockSignalType,
			),
		)
	}
	clockLogic.WriteString(fmt.Sprintf("        %s.step(); // clock low\n", instanceName))
	for _, clockPort := range clockPortNames {
		clockLogic.WriteString(
			fmt.Sprintf(
				"        %s.p_%s.set<%s>(true);\n",
				instanceName,
				clockPort,
				clockSignalType,
			),
		)
	}
	clockLogic.WriteString(fmt.Sprintf("        %s.step(); // clock high\n", instanceName))
	clockLogic.WriteString("    }\n")
	return clockLogic.String()
}

func (g *Generator) generateCXXRTLOutputWrites(instanceName string, outputDir string) string {
	var outputWrites strings.Builder
	for _, port := range g.module.Ports {
		if port.Direction == verilog.OUTPUT {
			portName := strings.TrimSpace(port.Name)
			fileName := fmt.Sprintf("output_%s.hex", portName)
			cppType := getCXXRTLPortType(port.Width)

			outputWrites.WriteString(fmt.Sprintf(`    std::ofstream %s_file("%s/%s");
    if (!%s_file.is_open()) {
        std::cerr << "Error opening output file: %s" << std::endl;
        return 1;
    }
`, portName, outputDir, fileName, portName, fileName))

			if port.Width > 1 {
				outputWrites.WriteString(
					fmt.Sprintf("    %s_file << std::hex << %s.p_%s.get<%s>();\n",
						portName, instanceName, portName, cppType),
				)
			} else {
				outputWrites.WriteString(fmt.Sprintf("    %s_file << (%s.p_%s.get<%s>() ? '1' : '0');\n",
					portName, instanceName, portName, cppType))
			}
			outputWrites.WriteString(fmt.Sprintf("    %s_file.close();\n", portName))
		}
	}
	return outputWrites.String()
}

// GenerateCXXRTLTestbench creates the C++ testbench for CXXRTL in the specified directory
func (g *Generator) GenerateCXXRTLTestbench(outputDir string) error {
	instanceName := g.module.Name + "_i" // e.g., my_module_i

	inputDeclsStr := g.generateCXXRTLInputDeclarations()
	inputReadsStr := g.generateCXXRTLInputReads(outputDir)
	inputApplyStr := g.generateCXXRTLInputApply(instanceName)

	// Identify clock and reset ports
	// Note: identifyClockAndResetPorts is from the SV part, but its logic is generic enough.
	// We can reuse it here.
	svClockPorts, svResetPort, svIsActiveHigh := g.identifyClockAndResetPorts()

	// For CXXRTL, we might need to adapt how we use these.
	// The reset identification logic is similar.
	var cxxrtlResetName string
	var cxxrtlIsActiveHigh bool
	// Re-iterate for reset specifically for CXXRTL if different logic is ever needed,
	// or directly use svResetPort and svIsActiveHigh if the identification is identical.
	// For now, let's assume the SV identification is sufficient.
	if svResetPort != "" {
		cxxrtlResetName = svResetPort
		cxxrtlIsActiveHigh = svIsActiveHigh
	}

	resetLogicStr := g.generateCXXRTLResetLogic(instanceName, cxxrtlResetName, cxxrtlIsActiveHigh)

	// Identify clock ports for CXXRTL by filtering svClockPorts to exclude the reset port.
	var cxxrtlClockPortNames []string
	for _, clkPort := range svClockPorts {
		if clkPort == cxxrtlResetName { // Skip if the clock port is also the identified reset port
			continue
		}
		cxxrtlClockPortNames = append(cxxrtlClockPortNames, clkPort)
	}

	// If cxxrtlClockPortNames is empty after filtering, it means all ports identified by
	// svClockPorts might have been the reset port, or no clocks were found initially.
	// The generateCXXRTLClockLogic function already handles the case of empty clockPortNames.

	clockLogicStr := g.generateCXXRTLClockLogic(instanceName, cxxrtlClockPortNames)

	var clockAndResetHandling strings.Builder
	clockAndResetHandling.WriteString(resetLogicStr)
	clockAndResetHandling.WriteString(clockLogicStr)

	outputWritesStr := g.generateCXXRTLOutputWrites(instanceName, outputDir)

	// Apply the generated code to the template
	testbench := fmt.Sprintf(cxxrtlTestbenchTemplate,
		g.module.Name,                  // 1. For #include "%s.h"
		g.module.Name,                  // 2. For cxxrtl_design::p_%s
		instanceName,                   // 3. For instance name %s_i
		inputDeclsStr,                  // 4.
		inputReadsStr,                  // 5.
		inputApplyStr,                  // 6.
		clockAndResetHandling.String(), // 7.
		outputWritesStr)                // 8.

	// Write to the specified output directory
	cppTestbenchPath := filepath.Join(outputDir, "testbench.cpp")
	return utils.WriteFileContent(cppTestbenchPath, testbench)
}

// Helper function to find the smallest standard integer size (8, 16, 32, 64)
// that can accommodate n bits. (This function is still useful for declarations)
func nextPowerOfTwo(n int) int {
	if n <= 0 {
		// Default to 8 for non-positive or zero widths
		return 8
	}
	size := 8
	// Use a loop to find the smallest standard size (8, 16, 32, 64)
	// that is greater than or equal to n.
	// Keep doubling the size as long as it's smaller than n
	// and the size itself hasn't reached the maximum standard size (64).
	for size < n && size < 64 {
		size *= 2 // Double the size
	}

	// At this point, either size >= n, or size has reached 64.
	// If n was greater than 64, the loop stopped because size hit 64.
	// In either case, 'size' holds the appropriate standard C++ integer bit width (up to 64).
	// We return 64 for any n > 32.
	return size
}
