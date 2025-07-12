package testgen

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

// TestbenchConfig holds configuration for safe testbench generation
type TestbenchConfig struct {
	MaxClockCycles    int     // Maximum number of clock cycles to prevent infinite loops
	MaxCombLoopChecks int     // Maximum combinational evaluation steps
	MaxEvaluationTime int     // Maximum evaluation time in time units
	ClockPeriod       int     // Clock period in time units
	SettlingTime      int     // Time to allow for signal settling
	TimeoutMultiplier float64 // Multiplier for timeout calculation
}

// DefaultTestbenchConfig returns safe default configuration values
func DefaultTestbenchConfig() *TestbenchConfig {
	return &TestbenchConfig{
		MaxClockCycles:    50,   // Increased from 10 for more comprehensive testing, but still bounded
		MaxCombLoopChecks: 20,   // Maximum steps for combinational logic to settle
		MaxEvaluationTime: 1000, // Maximum simulation time in time units
		ClockPeriod:       10,   // Clock period (5 low + 5 high)
		SettlingTime:      20,   // Additional settling time
		TimeoutMultiplier: 1.5,  // 50% safety margin on timeouts
	}
}

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
	config   *TestbenchConfig
	svFile   *verilog.VerilogFile
}

// NewGenerator creates a new testbench generator
func NewGenerator(module *verilog.Module, fileName string, svFile *verilog.VerilogFile) *Generator {
	// We don't need to extract enums here anymore since they're embedded in the mocked file
	return &Generator{
		module:   module,
		fileName: fileName,
		config:   DefaultTestbenchConfig(),
		svFile:   svFile,
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
		portName := strings.TrimSpace(port.Name)
		var finalDeclarationString string

		// Handle interface ports differently
		switch port.Type {
		case verilog.INTERFACE: // nolint: default
			// For interface ports, instantiate the interface itself
			finalDeclarationString = fmt.Sprintf("%s %s();", port.InterfaceName, portName)
		case verilog.REAL, verilog.SHORTREAL, verilog.REALTIME: // Handle real type
			finalDeclarationString = fmt.Sprintf("real %s;", portName)
		default:
			// Determine the target width for regular ports
			targetWidth := port.Width // Start with the width from the parser

			// If the parsed width is 0 or 1, it might not be the full width for certain types.
			// We consult GetWidthForType to get a default width for the Verilog type.
			if targetWidth <= 1 {
				// Assuming verilog.GetWidthForType is available as per the user's context.
				// This function provides default widths (e.g., INT=32, BYTE=8, LOGIC=1).
				defaultWidthForType := verilog.GetWidthForType(port.Type)
				if defaultWidthForType > targetWidth {
					targetWidth = defaultWidthForType
				}
			}

			// Generate the SystemVerilog declaration string
			if targetWidth > 1 {
				finalDeclarationString = fmt.Sprintf("logic [%d:0] %s;", targetWidth-1, portName)
			} else {
				// Handles targetWidth == 1 (e.g. for single bit logic, reg, or byte with width 1 if GetWidthForType returned 1)
				// Also handles targetWidth == 0 as a fallback (e.g. for UNKNOWN type if port.Width was also 0)
				finalDeclarationString = fmt.Sprintf("logic %s;", portName)
			}
		}

		declarations.WriteString(fmt.Sprintf("    %s\n", finalDeclarationString))
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
			if param.Name == "" || param.Name == "unsigned" || param.Name == "signed" ||
				param.DefaultValue != "" {
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

			// Handle interface ports differently - generate protocol-aware stimulus
			if port.Type == verilog.INTERFACE {
				inputCount++
				// Generate meaningful interface stimulus based on modport
				interfaceStimulus := g.GenerateInterfaceStimulus(port)
				inputReads.WriteString(interfaceStimulus)
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

			if port.Type == verilog.REAL || port.Type == verilog.SHORTREAL ||
				port.Type == verilog.REALTIME { // Handle real type
				inputReads.WriteString(
					fmt.Sprintf("status = $sscanf(line, \"%%f\", %s);\n", portName),
				)
			} else {
				inputReads.WriteString(
					fmt.Sprintf("status = $sscanf(line, \"%%h\", %s);\n", portName),
				)
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

// generateSVClockToggling generates code to toggle clock signals with safeguards
func (g *Generator) generateSVClockToggling(clockPorts []string) string {
	if len(clockPorts) == 0 {
		// If no clock ports, just add a delay
		return fmt.Sprintf(
			"\n        // Allow module to process\n        #%d;\n",
			g.config.SettlingTime,
		)
	}

	var clockToggle strings.Builder
	clockToggle.WriteString(
		"\n        // Toggle clocks for several cycles with timeout protection\n",
	)

	// Add simulation timeout based on configuration
	maxSimTime := g.config.MaxClockCycles*g.config.ClockPeriod + g.config.SettlingTime
	timeoutTime := int(float64(maxSimTime) * g.config.TimeoutMultiplier)

	clockToggle.WriteString(
		"        // Set simulation timeout to prevent infinite loops\n",
	)
	clockToggle.WriteString("        fork\n")
	clockToggle.WriteString("            begin\n")
	clockToggle.WriteString(fmt.Sprintf("                #%d;\n", timeoutTime))
	clockToggle.WriteString(
		fmt.Sprintf(
			"                $display(\"ERROR: Simulation timeout after %d time units\");\n",
			timeoutTime,
		),
	)
	clockToggle.WriteString("                $finish;\n")
	clockToggle.WriteString("            end\n")
	clockToggle.WriteString("            begin\n")

	clockToggle.WriteString(
		fmt.Sprintf("                repeat (%d) begin\n", g.config.MaxClockCycles),
	)

	for _, clockPort := range clockPorts {
		clockToggle.WriteString(fmt.Sprintf("                    %s = 0;\n", clockPort))
	}
	clockToggle.WriteString(fmt.Sprintf("                    #%d;\n", g.config.ClockPeriod/2))

	for _, clockPort := range clockPorts {
		clockToggle.WriteString(fmt.Sprintf("                    %s = 1;\n", clockPort))
	}
	clockToggle.WriteString(fmt.Sprintf("                    #%d;\n", g.config.ClockPeriod/2))

	clockToggle.WriteString("                end\n")
	clockToggle.WriteString("            end\n")
	clockToggle.WriteString("        join_any\n")
	clockToggle.WriteString("        disable fork; // Kill timeout process\n")

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
        if (fd == 0) begin
            $display("Error: Unable to open output file '%s' for port '%s'.", "%s", "%s");
            $finish;
        end
`, fileName, fileName, portName, fileName, portName)) // Corrected $display arguments

			if port.Type == verilog.REAL || port.Type == verilog.SHORTREAL ||
				port.Type == verilog.REALTIME { // Handle real type
				outputWrites.WriteString(
					fmt.Sprintf("        $fwrite(fd, \"%%f\\n\", %s);\n", portName),
				)
			} else {
				// Determine the width for writing logic
				effectiveWidth := port.Width
				// Consistent with CXXRTL and SV input declaration width logic for types like int
				if port.Type == verilog.INT || port.Type == verilog.INTEGER {
					effectiveWidth = 32
				} else if effectiveWidth == 0 { // Default for 0-width (e.g. 'logic my_signal;') which is 1-bit
					effectiveWidth = 1
				}

				if effectiveWidth > 1 {
					// For multi-bit ports, write each bit from MSB to LSB
					outputWrites.WriteString(
						fmt.Sprintf("        for (int i = %d; i >= 0; i--) begin\n", effectiveWidth-1),
					)
					outputWrites.WriteString(
						fmt.Sprintf("            $fwrite(fd, \"%%b\", %s[i]);\n", portName),
					)
					outputWrites.WriteString("        end\n")
					outputWrites.WriteString(
						"        $fwrite(fd, \"\\n\");",
					)
				} else { // effectiveWidth is 1
					outputWrites.WriteString(fmt.Sprintf("        $fwrite(fd, \"%%b\\n\", %s);\n", portName))
				}
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

	testbench := fmt.Sprintf(svTestbenchTemplate,
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
	if err := utils.WriteFileContent(svTestbenchPath, testbench); err != nil {
		return fmt.Errorf(
			"failed to write SystemVerilog testbench to %s: %w",
			svTestbenchPath,
			err,
		)
	}
	return nil
}

// GenerateSVTestbenchWithInputs generates a SystemVerilog testbench that hardcodes input values from a map
// Instead of reading from input files, it assigns values directly to the input ports
func (g *Generator) GenerateSVTestbenchWithInputs(inputs map[string]string) string {
	declarations := g.generateSVPortDeclarations()
	moduleInst := g.generateSVModuleInstantiation()
	clockPorts, resetPort, isActiveHigh := g.identifyClockAndResetPorts()

	// Generate SystemVerilog code to assign these values
	var inputAssigns strings.Builder
	inputCount := 0
	for _, port := range g.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			portName := strings.TrimSpace(port.Name)
			if val, ok := inputs[portName]; ok {
				if port.Type == verilog.REAL || port.Type == verilog.REALTIME ||
					port.Type == verilog.SHORTREAL { // Handle real types
					inputAssigns.WriteString(fmt.Sprintf("        %s = %s;\n", portName, val))
				} else {
					inputAssigns.WriteString(fmt.Sprintf("        %s = 'h%s;\n", portName, val))
				}
				inputCount++
			} else {
				inputAssigns.WriteString(fmt.Sprintf("        %s = 0;\n", portName))
			}
		}
	}

	resetToggleStr := g.generateSVResetToggling(resetPort, isActiveHigh)
	clockToggleStr := g.generateSVClockToggling(clockPorts)
	outputWritesStr, outputCount := g.generateSVOutputWrites()

	testbench := fmt.Sprintf(svTestbenchTemplate,
		declarations,
		moduleInst,
		inputCount,
		inputAssigns.String(),
		resetToggleStr,
		clockToggleStr,
		outputCount,
		outputWritesStr,
	)
	return testbench
}

// getCXXRTLTestbenchVarType returns the C++ variable type for testbench variables
// These are simple C++ types used to hold values before applying them to CXXRTL ports
func getCXXRTLTestbenchVarType(port *verilog.Port) string {
	width := port.Width

	// Correct width for specific Verilog types if parser defaults width to 0 or an incorrect value.
	switch port.Type {
	case verilog.REAL, verilog.REALTIME:
		return "double"
	case verilog.SHORTREAL:
		return "float"
	case verilog.INT, verilog.INTEGER:
		width = 32
	case verilog.BYTE:
		width = 8
	case verilog.SHORTINT:
		width = 16
	case verilog.LONGINT, verilog.TIME:
		width = 64
	case verilog.LOGIC, verilog.BIT, verilog.REG, verilog.WIRE:
		if width == 0 {
			width = 1
		}
	case verilog.UNKNOWN, verilog.STRING, verilog.STRUCT, verilog.VOID, verilog.ENUM,
		verilog.USERDEFINED, verilog.TYPE, verilog.INTERFACE:
		// Handle other types or fall through
		if width == 0 {
			width = 1
		}
	}

	if width == 1 {
		return "bool"
	}
	// For multi-bit ports, use standard C++ types
	switch {
	case width <= 8:
		return "uint8_t"
	case width <= 16:
		return "uint16_t"
	case width <= 32:
		return "uint32_t"
	case width <= 64:
		return "uint64_t"
	default:
		// For very wide signals, use CXXRTL value type
		return fmt.Sprintf("cxxrtl::value<%d>", width)
	}
}

// getCXXRTLAccessMethod returns template-based function name for reading port values
func getCXXRTLAccessMethod() string {
	// Return template-based function name for bit access or value access
	return "_get_port_value"
}

// getCXXRTLSetMethod returns template-based function name to set port values
func getCXXRTLSetMethod(port *verilog.Port) string {
	width := port.Width

	// Correct width for specific Verilog types
	switch {
	case port.Type == verilog.INT || port.Type == verilog.INTEGER:
		width = 32
	case (port.Type == verilog.LOGIC || port.Type == verilog.BIT || port.Type == verilog.REG || port.Type == verilog.WIRE) && width == 0:
		width = 1
	case width == 0:
		width = 1
	}

	// Return template-based function name that works with both value<> and wire<>
	switch port.Type {
	case verilog.REAL, verilog.REALTIME:
		return "_set_port_value<double>"
	case verilog.SHORTREAL:
		return "_set_port_value<float>"
	}

	if width == 1 {
		return "_set_port_value<bool>"
	}
	// For multi-bit ports, use standard C++ types
	switch {
	case width <= 8:
		return "_set_port_value<uint8_t>"
	case width <= 16:
		return "_set_port_value<uint16_t>"
	case width <= 32:
		return "_set_port_value<uint32_t>"
	case width <= 64:
		return "_set_port_value<uint64_t>"
	default:
		return "_set_port_value_wide"
	}
}

func (g *Generator) generateCXXRTLInputDeclarations() string {
	var inputDecls strings.Builder
	for _, port := range g.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			portName := strings.TrimSpace(port.Name)
			varDeclType := getCXXRTLTestbenchVarType(port) // Use testbench variable type
			inputDecls.WriteString(fmt.Sprintf("    %s %s;\n", varDeclType, portName))
		}
	}
	return inputDecls.String()
}

func (g *Generator) generateCXXRTLInputReads() string {
	var inputReads strings.Builder
	for _, port := range g.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			portName := strings.TrimSpace(port.Name)
			fileName := fmt.Sprintf("input_%s.hex", portName)
			cppFilePath := strings.ReplaceAll(fileName, "\\", "\\\\")
			varDeclType := getCXXRTLTestbenchVarType(port)

			// Determine effective width
			width := port.Width
			if port.Type == verilog.INT || port.Type == verilog.INTEGER {
				width = 32
			} else if width == 0 {
				width = 1
			}

			inputReads.WriteString(
				fmt.Sprintf("    std::ifstream %s_file(\"%s\");\n", portName, cppFilePath),
			)
			inputReads.WriteString(fmt.Sprintf("    if (!%s_file.is_open()) {\n", portName))
			inputReads.WriteString(
				fmt.Sprintf(
					"        std::cerr << \"Failed to open input file for %s: %s\" << std::endl;\n",
					portName,
					cppFilePath,
				),
			)
			inputReads.WriteString("        return 1;\n")
			inputReads.WriteString("    }\n")

			if port.Type == verilog.REAL || port.Type == verilog.REALTIME ||
				port.Type == verilog.SHORTREAL { // Handle real types
				inputReads.WriteString(
					fmt.Sprintf("    if (!(%s_file >> %s)) {\n", portName, portName),
				)
				inputReads.WriteString(
					fmt.Sprintf(
						"        std::cerr << \"Failed to parse float value for %s from input file: %s\" << std::endl;\n",
						portName,
						cppFilePath,
					),
				)
				inputReads.WriteString(fmt.Sprintf("        %s_file.close();\n", portName))
				inputReads.WriteString("        return 1;\n")
				inputReads.WriteString("    }\n")
			} else {
				inputReads.WriteString(fmt.Sprintf("    std::string %s_hex_str;\n", portName))
				inputReads.WriteString(fmt.Sprintf("    %s_file >> %s_hex_str;\n", portName, portName))

				// Add error checking for file read
				inputReads.WriteString(
					fmt.Sprintf("    if (%s_file.fail() && !%s_file.eof()) {\n", portName, portName),
				)
				inputReads.WriteString(
					fmt.Sprintf(
						"        std::cerr << \"Failed to read hex string for %s from input file: %s\" << std::endl;\n",
						portName,
						cppFilePath,
					),
				)
				inputReads.WriteString(fmt.Sprintf("        %s_file.close();\n", portName))
				inputReads.WriteString("        return 1;\n")
				inputReads.WriteString("    }\n")

				// Handle different width cases
				if strings.HasPrefix(varDeclType, "cxxrtl::value<") {
					// Wide signal - parse using chunk-based method
					inputReads.WriteString(
						fmt.Sprintf("    // Parse %s_hex_str into %s.data\n", portName, portName),
					)
					inputReads.WriteString(
						fmt.Sprintf(
							"    // %s is %s. Chunks = %d (assuming 64-bit chunks). Bits per chunk = 64. Hex chars per chunk = 16.\n",
							portName,
							varDeclType,
							(width+63)/64,
						),
					)
					inputReads.WriteString(
						fmt.Sprintf("    // Total hex chars for %d bits = %d.\n", width, (width+3)/4),
					)
					inputReads.WriteString(
						"    // Hex string is MSB first. CXXRTL data array is LSB first (data[0] is LSB chunk).\n",
					)
					inputReads.WriteString(
						fmt.Sprintf("    size_t total_hex_chars_for_%s = %d / 4;\n", portName, width),
					)
					inputReads.WriteString(
						fmt.Sprintf(
							"    if (%s_hex_str.length() < total_hex_chars_for_%s) {\n",
							portName,
							portName,
						),
					)
					inputReads.WriteString(
						fmt.Sprintf(
							"        %s_hex_str.insert(0, total_hex_chars_for_%s - %s_hex_str.length(), '0');\n",
							portName,
							portName,
							portName,
						),
					)
					inputReads.WriteString(
						fmt.Sprintf(
							"    } else if (%s_hex_str.length() > total_hex_chars_for_%s) {\n",
							portName,
							portName,
						),
					)
					inputReads.WriteString(
						fmt.Sprintf(
							"        %s_hex_str = %s_hex_str.substr(%s_hex_str.length() - total_hex_chars_for_%s);\n",
							portName,
							portName,
							portName,
							portName,
						),
					)
					inputReads.WriteString("    }\n\n")

					inputReads.WriteString(
						fmt.Sprintf(
							"    const size_t num_chunks_for_%s = %s::chunks;\n",
							portName,
							varDeclType,
						),
					)
					inputReads.WriteString(
						fmt.Sprintf(
							"    const size_t hex_chars_per_chunk_for_%s = %s::chunk::bits / 4;\n",
							portName,
							varDeclType,
						),
					)
					inputReads.WriteString("\n")
					inputReads.WriteString(
						fmt.Sprintf("    for (size_t i = 0; i < num_chunks_for_%s; ++i) {\n", portName),
					)
					inputReads.WriteString(
						"        size_t data_idx = i; // LSB chunk for data is data[0]\n",
					)
					inputReads.WriteString(
						fmt.Sprintf(
							"        size_t str_offset = (num_chunks_for_%s - 1 - i) * hex_chars_per_chunk_for_%s; // Corresponding part in MSB-first hex string\n",
							portName,
							portName,
						),
					)
					inputReads.WriteString(
						fmt.Sprintf(
							"        std::string chunk_hex_str = %s_hex_str.substr(str_offset, hex_chars_per_chunk_for_%s);\n",
							portName,
							portName,
						),
					)
					inputReads.WriteString(
						fmt.Sprintf(
							"        %s.data[data_idx] = std::stoull(chunk_hex_str, nullptr, 16);\n",
							portName,
						),
					)
					inputReads.WriteString("    }\n")
				} else {
					// Standard integer types
					inputReads.WriteString(fmt.Sprintf("    std::stringstream ss_%s;\n", portName))
					inputReads.WriteString(fmt.Sprintf("    ss_%s << std::hex << %s_hex_str;\n", portName, portName))

					if varDeclType == "uint8_t" || varDeclType == "bool" {
						inputReads.WriteString(fmt.Sprintf("    unsigned int temp_%s;\n", portName))
						inputReads.WriteString(fmt.Sprintf("    if (!(ss_%s >> temp_%s)) {\n", portName, portName))
						inputReads.WriteString(fmt.Sprintf("        std::cerr << \"Failed to parse hex value for %s: \" << %s_hex_str << std::endl;\n", portName, portName))
						inputReads.WriteString(fmt.Sprintf("        %s_file.close();\n", portName))
						inputReads.WriteString("        return 1;\n")
						inputReads.WriteString("    }\n")
						inputReads.WriteString(fmt.Sprintf("    %s = static_cast<%s>(temp_%s);\n", portName, varDeclType, portName))
					} else {
						inputReads.WriteString(fmt.Sprintf("    if (!(ss_%s >> %s)) {\n", portName, portName))
						inputReads.WriteString(fmt.Sprintf("        std::cerr << \"Failed to parse hex value for %s: \" << %s_hex_str << std::endl;\n", portName, portName))
						inputReads.WriteString(fmt.Sprintf("        %s_file.close();\n", portName))
						inputReads.WriteString("        return 1;\n")
						inputReads.WriteString("    }\n")
					}
				}
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
			mangledPortName := cxxrtlManglePortName(portName)
			setMethod := getCXXRTLSetMethod(port)

			inputApply.WriteString(
				fmt.Sprintf(
					"    %s(%s.%s, %s);\n",
					setMethod,
					instanceName,
					mangledPortName,
					portName,
				),
			)
		}
	}
	inputApply.WriteString("    // Input application\n")
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
			"\n    // No clock found, performing bounded steps for combinational logic to settle\n",
		)
		// Use bounded loop for combinational settling to prevent infinite loops
		noClockLogic.WriteString(
			fmt.Sprintf(
				"    for (int settle_step = 0; settle_step < %d; settle_step++) {\n",
				g.config.MaxCombLoopChecks,
			),
		)
		noClockLogic.WriteString(fmt.Sprintf("        %s.step();\n", instanceName))
		noClockLogic.WriteString("    }\n")
		return noClockLogic.String()
	}

	var clockLogic strings.Builder
	clockLogic.WriteString(
		"\n    // Clock toggling with bounded cycles to prevent infinite loops\n",
	)
	clockLogic.WriteString(
		fmt.Sprintf("    for (int cycle = 0; cycle < %d; cycle++) {\n", g.config.MaxClockCycles),
	)

	for _, clockPort := range clockPortNames {
		mangledClockPortName := cxxrtlManglePortName(clockPort)
		// Find the actual port to get its set method
		var setMethodLow string
		for _, port := range g.module.Ports {
			if strings.TrimSpace(port.Name) == clockPort {
				setMethodLow = getCXXRTLSetMethod(port)
				break
			}
		}

		clockLogic.WriteString(
			fmt.Sprintf(
				"        %s(%s.%s, false);\n",
				setMethodLow,
				instanceName,
				mangledClockPortName,
			),
		)
	}
	clockLogic.WriteString(fmt.Sprintf("        %s.step(); // clock low\n", instanceName))

	for _, clockPort := range clockPortNames {
		mangledClockPortName := cxxrtlManglePortName(clockPort)
		// Find the actual port to get its set method
		var setMethodHigh string
		for _, port := range g.module.Ports {
			if strings.TrimSpace(port.Name) == clockPort {
				setMethodHigh = getCXXRTLSetMethod(port)
				break
			}
		}

		clockLogic.WriteString(
			fmt.Sprintf(
				"        %s(%s.%s, true);\n",
				setMethodHigh,
				instanceName,
				mangledClockPortName,
			),
		)
	}
	clockLogic.WriteString(fmt.Sprintf("        %s.step(); // clock high\n", instanceName))
	clockLogic.WriteString("    }\n")

	// Add bounded evaluation steps to ensure all logic settles
	clockLogic.WriteString(
		fmt.Sprintf(
			"\n    // Bounded evaluation steps to ensure all logic settles (max %d steps)\n",
			g.config.MaxCombLoopChecks,
		),
	)
	clockLogic.WriteString(
		fmt.Sprintf(
			"    for (int settle_step = 0; settle_step < %d; settle_step++) {\n",
			g.config.MaxCombLoopChecks,
		),
	)
	clockLogic.WriteString(fmt.Sprintf("        %s.step();\n", instanceName))
	clockLogic.WriteString("    }\n")

	return clockLogic.String()
}

func (g *Generator) generateCXXRTLOutputWrites(instanceName string) string {
	var outputWrites strings.Builder
	for _, port := range g.module.Ports {
		if port.Direction == verilog.OUTPUT {
			portName := strings.TrimSpace(port.Name)
			fileName := fmt.Sprintf("output_%s.hex", portName)
			cppFilePath := strings.ReplaceAll(fileName, "\\", "\\\\")

			outputWrites.WriteString(
				fmt.Sprintf("    std::ofstream %s_file(\"%s\");\n", portName, cppFilePath),
			)
			outputWrites.WriteString(fmt.Sprintf("    if (!%s_file.is_open()) {\n", portName))
			outputWrites.WriteString(
				fmt.Sprintf(
					"        std::cerr << \"Failed to open output file for %s: %s\" << std::endl;\n",
					portName,
					cppFilePath,
				),
			)
			outputWrites.WriteString(
				"        return 1;\n",
			) // This return needs to be handled, maybe return error instead?
			outputWrites.WriteString("    }\n")

			if port.Type == verilog.REAL || port.Type == verilog.REALTIME ||
				port.Type == verilog.SHORTREAL { // Handle real types
				outputWrites.WriteString(
					fmt.Sprintf(
						"    %s_file << %s.%s.get<double>() << std::endl;\n",
						portName,
						instanceName,
						cxxrtlManglePortName(portName),
					),
				)
			} else {
				// Determine the width for writing logic
				effectiveWidth := port.Width
				mangledPortName := cxxrtlManglePortName(portName)
				accessMethod := getCXXRTLAccessMethod()

				// Consistent with CXXRTL and SV input declaration width logic for types like int
				if port.Type == verilog.INT || port.Type == verilog.INTEGER {
					effectiveWidth = 32
				} else if effectiveWidth == 0 { // Default for 0-width (e.g. 'logic my_signal;') which is 1-bit
					effectiveWidth = 1
				}

				// Use template-based helper to get port value and write bits MSB to LSB
				if effectiveWidth > 1 {
					outputWrites.WriteString(
						fmt.Sprintf("    for (int i = %d; i >= 0; --i) {\n", effectiveWidth-1),
					)
					outputWrites.WriteString(
						fmt.Sprintf(
							"        %s_file << (%s(%s.%s, i) ? '1' : '0');\n",
							portName,
							accessMethod,
							instanceName,
							mangledPortName,
						),
					)
					outputWrites.WriteString("    }\n")
					outputWrites.WriteString(fmt.Sprintf("    %s_file << std::endl;\n", portName))
				} else { // Single-bit ports
					outputWrites.WriteString(
						fmt.Sprintf(
							"    %s_file << (%s(%s.%s, 0) ? '1' : '0') << std::endl;\n",
							portName,
							accessMethod,
							instanceName,
							mangledPortName,
						),
					)
				}
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
	inputReadsStr := g.generateCXXRTLInputReads()
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

// GenerateInterfaceStimulus generates protocol-aware stimulus for interface ports
func (g *Generator) GenerateInterfaceStimulus(port *verilog.Port) string {
	var stimulus strings.Builder
	portName := strings.TrimSpace(port.Name)

	// Find the interface definition to understand its signals
	var intf *verilog.Interface
	for _, i := range g.svFile.Interfaces {
		if i.Name == port.InterfaceName {
			intf = i
			break
		}
	}

	if intf == nil {
		// Fallback: if we can't find the interface, initialize to safe defaults
		stimulus.WriteString(
			fmt.Sprintf(
				"        // Interface %s not found, using safe defaults\n",
				port.InterfaceName,
			),
		)
		stimulus.WriteString(fmt.Sprintf("        %s.data = 8'h00;\n", portName))
		stimulus.WriteString(fmt.Sprintf("        %s.valid = 1'b0;\n", portName))
		stimulus.WriteString(fmt.Sprintf("        %s.ready = 1'b0;\n", portName))
		return stimulus.String()
	}

	// Generate stimulus based on modport and interface signals
	stimulus.WriteString(
		fmt.Sprintf(
			"        // Initialize interface %s (%s.%s)\n",
			portName,
			port.InterfaceName,
			port.ModportName,
		),
	)

	// Find the modport to understand signal directions
	var modport *verilog.ModPort
	for _, mp := range intf.ModPorts {
		if mp.Name == port.ModportName {
			modport = mp
			break
		}
	}

	if modport != nil {
		// Generate stimulus based on modport signals
		for _, signal := range modport.Signals {
			signalName := fmt.Sprintf("%s.%s", portName, signal.Name)

			// Only drive signals that are outputs from the modport perspective
			// (inputs to the module from the testbench perspective)
			if signal.Direction == verilog.OUTPUT {
				// Find the signal width from interface variables
				signalWidth := 1 // default width
				for _, variable := range intf.Variables {
					if variable.Name == signal.Name {
						signalWidth = variable.Width
						break
					}
				}

				// Generate appropriate stimulus based on signal name and width
				switch signal.Name {
				case "data":
					stimulus.WriteString(
						fmt.Sprintf("        %s = %d'h%02X;\n", signalName, signalWidth, 0x55),
					) // Pattern value
				case "valid":
					stimulus.WriteString(
						fmt.Sprintf("        %s = 1'b1;\n", signalName),
					) // Start with valid data
				case "ready":
					stimulus.WriteString(
						fmt.Sprintf("        %s = 1'b1;\n", signalName),
					) // Ready to receive
				default:
					// Generic initialization for other signals
					if signalWidth <= 1 {
						stimulus.WriteString(fmt.Sprintf("        %s = 1'b0;\n", signalName))
					} else {
						stimulus.WriteString(fmt.Sprintf("        %s = %d'h00;\n", signalName, signalWidth))
					}
				}
			}
		}
	} else {
		// Fallback: if modport not found, initialize common interface signals
		stimulus.WriteString(fmt.Sprintf("        // Modport %s not found, using common defaults\n", port.ModportName))

		// Look for common interface signals in variables
		for _, variable := range intf.Variables {
			signalName := fmt.Sprintf("%s.%s", portName, variable.Name)
			switch variable.Name {
			case "data":
				stimulus.WriteString(fmt.Sprintf("        %s = %d'h55;\n", signalName, variable.Width))
			case "valid":
				stimulus.WriteString(fmt.Sprintf("        %s = 1'b1;\n", signalName))
			case "ready":
				stimulus.WriteString(fmt.Sprintf("        %s = 1'b1;\n", signalName))
			default:
				if variable.Width <= 1 {
					stimulus.WriteString(fmt.Sprintf("        %s = 1'b0;\n", signalName))
				} else {
					stimulus.WriteString(fmt.Sprintf("        %s = %d'h00;\n", signalName, variable.Width))
				}
			}
		}
	}

	return stimulus.String()
}
