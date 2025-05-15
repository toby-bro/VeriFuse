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

// GenerateTestbenches creates both SystemVerilog and C++ testbenches in the default TMP_DIR
func (g *Generator) GenerateTestbenches() error {
	return g.GenerateTestbenchesInDir(utils.TMP_DIR)
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
		var typeDecl string
		// Ensure we're declaring the right bit width for each port
		if port.Width > 1 {
			typeDecl = fmt.Sprintf("logic [%d:0] ", port.Width-1)
		} else {
			typeDecl = "logic "
		}

		// Clean port name
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
