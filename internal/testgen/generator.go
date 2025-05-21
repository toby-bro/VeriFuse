package testgen

import (
	"fmt"
	"log"
	"os"
	"path/filepath"
	"strings"

	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

// cxxrtlMangleIdentifier replaces single underscores with double underscores.
func cxxrtlMangleIdentifier(name string) string {
	return strings.ReplaceAll(name, "_", "__")
}

// cxxrtlManglePortName creates the CXXRTL mangled version of a Verilog port name (e.g., i_val -> p_i__val).
func cxxrtlManglePortName(verilogPortName string) string {
	return "p_" + cxxrtlMangleIdentifier(verilogPortName)
}

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
// It now takes the whole port to infer width for types like 'int'.
func getCXXRTLPortType(port *verilog.Port) string {
	width := port.Width

	// Correct width for specific Verilog types if parser defaults width to 0 or an incorrect value.
	// Assuming verilog.Port has a 'Type' field of type verilog.PrimType (e.g., verilog.INT, verilog.LOGIC)
	// This part is crucial and depends on the actual structure of your verilog.Port
	if port.Type == verilog.INT ||
		port.Type == verilog.INTEGER { // Check if port.Type is comparable to these constants
		width = 32
	} else if (port.Type == verilog.LOGIC || port.Type == verilog.BIT || port.Type == verilog.REG || port.Type == verilog.WIRE) && width == 0 {
		width = 1 // Default for single-bit types if width was not specified or parsed as 0
	} else if width == 0 {
		// Fallback for other types if width is 0. This might indicate a parser issue for those types.
		// Defaulting to 32 here is a guess; ideally, the parser provides correct widths.
		// Or, this could be an error condition.
		// For now, to solve the 'int' issue primarily:
		// If not an int and width is 0, it's likely a single bit if it's a common type.
		// If it's some other complex type with width 0, that's a deeper parser issue.
		// Let's assume for now that if it's not 'int' and width is 0, it's probably meant to be 1.
		width = 1 // Cautious default for non-int, zero-width to bool/uint8_t if it falls through
	}

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
			varDeclType := getCXXRTLPortType(&port) // Pass pointer to port
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
			fileName := fmt.Sprintf("input_%s.hex", portName) // Changed filename format
			absFilePath, err := filepath.Abs(filepath.Join(outputDir, fileName))
			if err != nil {
				log.Fatalf("Failed to get absolute path for input file %s: %v", fileName, err)
			}

			// Ensure the directory exists
			if err := os.MkdirAll(filepath.Dir(absFilePath), 0o755); err != nil {
				log.Fatalf("Failed to create directory for input file: %v", err)
			}
			// Create an empty file if it doesn't exist, so the C++ testbench can open it.
			if _, err := os.Stat(absFilePath); os.IsNotExist(err) {
				f, err := os.Create(absFilePath)
				if err != nil {
					log.Fatalf("Failed to create empty input file %s: %v", absFilePath, err)
				}
				// Write a default value if it's a hex file, e.g., "0"
				if strings.HasSuffix(fileName, ".hex") {
					if _, wErr := f.WriteString("0\n"); wErr != nil {
						log.Fatalf("Failed to write default content to %s: %v", absFilePath, wErr)
					}
				}
				f.Close()
			}

			// Use the absolute path in the generated C++ code
			// Escape backslashes for Windows paths in C++ string literals
			cppFilePath := strings.ReplaceAll(absFilePath, "\\", "\\\\")

			inputReads.WriteString(
				fmt.Sprintf("    std::ifstream %s_file(\"%s\");\n", portName, cppFilePath),
			)
			inputReads.WriteString(fmt.Sprintf("    if (!%s_file.is_open()) {\n", portName))
			// In the C++ error message, also use the escaped path for clarity if it ever prints
			inputReads.WriteString(
				fmt.Sprintf(
					"        std::cerr << \"Failed to open input file for %s: %s\" << std::endl;\n",
					portName,
					cppFilePath,
				),
			)
			inputReads.WriteString("        return 1;\n")
			inputReads.WriteString("    }\n")

			// Determine the width for reading logic
			effectiveWidth := port.Width
			if port.Type == verilog.INT || port.Type == verilog.INTEGER {
				effectiveWidth = 32
			} else if effectiveWidth == 0 {
				effectiveWidth = 1 // Default for 0-width (likely single bit)
			}

			if effectiveWidth > 1 {
				inputReads.WriteString(fmt.Sprintf("    std::string %s_hex_str;\n", portName))
				inputReads.WriteString(
					fmt.Sprintf("    %s_file >> %s_hex_str;\n", portName, portName),
				)
				inputReads.WriteString(fmt.Sprintf("    std::stringstream ss_%s;\n", portName))
				inputReads.WriteString(
					fmt.Sprintf("    ss_%s << std::hex << %s_hex_str;\n", portName, portName),
				)
				inputReads.WriteString(fmt.Sprintf("    ss_%s >> %s;\n", portName, portName))
			} else {
				inputReads.WriteString(fmt.Sprintf("    %s_file >> %s;\n", portName, portName))
			}
			inputReads.WriteString(fmt.Sprintf("    %s_file.close();\n\n", portName))
		}
	}
	return inputReads.String()
}

func (g *Generator) generateCXXRTLInputApply(instanceName string) string {
	var inputApply strings.Builder
	for _, port := range g.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			portName := strings.TrimSpace(port.Name)
			cppType := getCXXRTLPortType(&port) // Pass pointer to port
			mangledPortName := cxxrtlManglePortName(portName)
			inputApply.WriteString(
				fmt.Sprintf(
					"    %s.%s.set<%s>(%s);\n",
					instanceName,
					mangledPortName,
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
	mangledResetPortName := cxxrtlManglePortName(resetPortName)
	resetLogic.WriteString(fmt.Sprintf("\n    // Toggle reset signal %s\n", mangledResetPortName))
	const resetSignalType = "bool" // Reset is single bit
	if isActiveHigh {
		resetLogic.WriteString(
			fmt.Sprintf(
				"    %s.%s.set<%s>(true); // Assert reset (active high)\n",
				instanceName,
				mangledResetPortName,
				resetSignalType,
			),
		)
	} else {
		resetLogic.WriteString(fmt.Sprintf("    %s.%s.set<%s>(false); // Assert reset (active low)\n", instanceName, mangledResetPortName, resetSignalType))
	}
	resetLogic.WriteString(
		fmt.Sprintf("    %s.step(); // Step to propagate reset assertion\n", instanceName),
	)

	if isActiveHigh {
		resetLogic.WriteString(
			fmt.Sprintf(
				"    %s.%s.set<%s>(false); // De-assert reset\n",
				instanceName,
				mangledResetPortName,
				resetSignalType,
			),
		)
	} else {
		resetLogic.WriteString(fmt.Sprintf("    %s.%s.set<%s>(true); // De-assert reset\n", instanceName, mangledResetPortName, resetSignalType))
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
			"\n    // No clock found, performing a few steps for combinational logic to settle\n",
		)
		noClockLogic.WriteString(fmt.Sprintf("    %s.step();\n", instanceName))
		noClockLogic.WriteString(fmt.Sprintf("    %s.step();\n", instanceName))
		return noClockLogic.String()
	}

	var clockLogic strings.Builder
	clockLogic.WriteString("\n    // Clock toggling\n")
	const clockSignalType = "bool" // Clock is single bit
	clockLogic.WriteString("    for (int cycle = 0; cycle < 10; cycle++) {\n")
	for _, clockPort := range clockPortNames {
		mangledClockPortName := cxxrtlManglePortName(clockPort)
		clockLogic.WriteString(
			fmt.Sprintf(
				"        %s.%s.set<%s>(false);\n",
				instanceName,
				mangledClockPortName,
				clockSignalType,
			),
		)
	}
	clockLogic.WriteString(fmt.Sprintf("        %s.step(); // clock low\n", instanceName))
	for _, clockPort := range clockPortNames {
		mangledClockPortName := cxxrtlManglePortName(clockPort)
		clockLogic.WriteString(
			fmt.Sprintf(
				"        %s.%s.set<%s>(true);\n",
				instanceName,
				mangledClockPortName,
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
			fileName := fmt.Sprintf("output_%s.hex", portName) // Changed filename format
			absFilePath, err := filepath.Abs(filepath.Join(outputDir, fileName))
			if err != nil {
				log.Fatalf("Failed to get absolute path for output file %s: %v", fileName, err)
			}

			// Ensure the directory exists
			if err := os.MkdirAll(filepath.Dir(absFilePath), 0o755); err != nil {
				log.Fatalf("Failed to create directory for output file: %v", err)
			}

			// Use the absolute path in the generated C++ code
			// Escape backslashes for Windows paths in C++ string literals
			cppFilePath := strings.ReplaceAll(absFilePath, "\\", "\\\\")

			outputWrites.WriteString(
				fmt.Sprintf("    std::ofstream %s_file(\"%s\");\n", portName, cppFilePath),
			)
			outputWrites.WriteString(fmt.Sprintf("    if (!%s_file.is_open()) {\n", portName))
			// In the C++ error message, also use the escaped path for clarity if it ever prints
			outputWrites.WriteString(
				fmt.Sprintf(
					"        std::cerr << \"Failed to open output file for %s: %s\" << std::endl;\n",
					portName,
					cppFilePath,
				),
			)
			outputWrites.WriteString("        return 1;\n")
			outputWrites.WriteString("    }\n")

			// Determine the width for writing logic
			effectiveWidth := port.Width
			cppType := getCXXRTLPortType(&port) // Pass pointer to port
			mangledPortName := cxxrtlManglePortName(portName)

			if port.Type == verilog.INT || port.Type == verilog.INTEGER {
				effectiveWidth = 32
			} else if effectiveWidth == 0 {
				effectiveWidth = 1 // Default for 0-width (likely single bit)
			}

			if effectiveWidth > 1 {
				hexWidth := (effectiveWidth + 3) / 4 // Calculate number of hex digits
				outputWrites.WriteString(
					fmt.Sprintf(
						"    %s_file << std::hex << std::setw(%d) << std::setfill('0') << %s.%s.get<%s>();\n",
						portName,
						hexWidth,
						instanceName,
						mangledPortName,
						cppType,
					),
				)
			} else {
				outputWrites.WriteString(fmt.Sprintf("    %s_file << (%s.%s.get<%s>() ? 1 : 0);\n",
					portName, instanceName, mangledPortName, cppType))
			}
			outputWrites.WriteString(fmt.Sprintf("    %s_file.close();\n\n", portName))
		}
	}
	return outputWrites.String()
}

// GenerateCXXRTLTestbench creates the C++ testbench for CXXRTL in the specified directory
func (g *Generator) GenerateCXXRTLTestbench(outputDir string) error {
	moduleNameForInclude := g.module.Name
	cxxrtlMangledModuleNameForClass := cxxrtlMangleIdentifier(g.module.Name)
	baseModuleNameForInstance := g.module.Name
	instanceName := baseModuleNameForInstance + "_i"

	inputDeclsStr := g.generateCXXRTLInputDeclarations()
	inputReadsStr := g.generateCXXRTLInputReads(
		outputDir,
	) // outputDir is for generator context, not hardcoded paths
	inputApplyStr := g.generateCXXRTLInputApply(instanceName)

	svClockPorts, svResetPort, svIsActiveHigh := g.identifyClockAndResetPorts()

	var cxxrtlResetName string
	var cxxrtlIsActiveHigh bool
	if svResetPort != "" {
		cxxrtlResetName = svResetPort
		cxxrtlIsActiveHigh = svIsActiveHigh
	}

	resetLogicStr := g.generateCXXRTLResetLogic(instanceName, cxxrtlResetName, cxxrtlIsActiveHigh)

	var cxxrtlClockPortNames []string
	for _, clkPort := range svClockPorts {
		if clkPort == cxxrtlResetName {
			continue
		}
		cxxrtlClockPortNames = append(cxxrtlClockPortNames, clkPort)
	}

	clockLogicStr := g.generateCXXRTLClockLogic(instanceName, cxxrtlClockPortNames)

	var clockAndResetHandling strings.Builder
	clockAndResetHandling.WriteString(resetLogicStr)
	clockAndResetHandling.WriteString(clockLogicStr)
	outputWritesStr := g.generateCXXRTLOutputWrites(
		instanceName,
		outputDir,
	) // outputDir is for generator context

	// Ensure the template uses "%s.h" for the include directive
	// This change should be in testbenches.go, but we ensure moduleNameForInclude is just the name.
	testbench := fmt.Sprintf(cxxrtlTestbenchTemplate,
		moduleNameForInclude,            // 1. For #include "%s.h" (template should have .h)
		cxxrtlMangledModuleNameForClass, // 2. For cxxrtl_design::p_%s
		baseModuleNameForInstance,       // 3. For instance name %s_i (template adds _i)
		inputDeclsStr,                   // 4.
		inputReadsStr,                   // 5.
		inputApplyStr,                   // 6.
		clockAndResetHandling.String(),  // 7.
		outputWritesStr)                 // 8.

	cppTestbenchPath := filepath.Join(outputDir, "testbench.cpp")
	return utils.WriteFileContent(cppTestbenchPath, testbench)
}
