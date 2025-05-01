package testgen

import (
	"fmt"
	"path/filepath"
	"strings"

	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

// Generator handles testbench generation
type Generator struct {
	module *verilog.Module
}

// NewGenerator creates a new testbench generator
func NewGenerator(module *verilog.Module) *Generator {
	// We don't need to extract enums here anymore since they're embedded in the mocked file
	return &Generator{
		module: module,
	}
}

// GenerateTestbenches creates both SystemVerilog and C++ testbenches
func (g *Generator) GenerateTestbenches() error {
	if err := g.GenerateSVTestbench(); err != nil {
		return fmt.Errorf("failed to generate SystemVerilog testbench: %v", err)
	}

	if err := g.GenerateCppTestbench(); err != nil {
		return fmt.Errorf("failed to generate C++ testbench: %v", err)
	}

	return nil
}

// GenerateSVTestbench creates the SystemVerilog testbench
func (g *Generator) GenerateSVTestbench() error {
	// Generate port declarations with proper widths
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

	// Create the module instance - use explicit port connections instead of .*
	var moduleInst strings.Builder
	moduleInst.WriteString(fmt.Sprintf("    %s", g.module.Name))
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
				// If no default value is provided in the source, use a reasonable default
				if strings.HasPrefix(strings.ToLower(param.Type), "int") {
					defaultVal = "1"
				} else if strings.HasPrefix(strings.ToLower(param.Type), "bit") {
					defaultVal = "1'b0"
				} else {
					defaultVal = "1"
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

	// Generate input file reading code
	var inputReads strings.Builder
	var inputCount int
	var clockPorts []string
	var resetPort string
	var isActiveHigh bool

	// First pass to identify clock and reset ports
	for _, port := range g.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			// Identify clock ports by name convention
			portName := strings.TrimSpace(port.Name)
			if strings.Contains(strings.ToLower(portName), "clk") ||
				strings.Contains(strings.ToLower(portName), "clock") {
				clockPorts = append(clockPorts, portName)
				continue
			}

			// Identify reset ports by name convention
			portNameLower := strings.ToLower(portName)
			if strings.Contains(portNameLower, "rst") || strings.Contains(portNameLower, "reset") {
				resetPort = portName
				// Determine if active high or low (active low has _n, _ni, or _l suffix)
				isActiveHigh = !(strings.HasSuffix(portNameLower, "_n") ||
					strings.HasSuffix(portNameLower, "_ni") ||
					strings.HasSuffix(portNameLower, "_l"))
			}
		}
	}

	// Generate input reading for non-clock ports
	for _, port := range g.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			portName := strings.TrimSpace(port.Name)

			// Skip clock ports, we'll handle them separately
			isClockPort := false
			for _, clockPort := range clockPorts {
				if portName == clockPort {
					isClockPort = true
					break
				}
			}

			if isClockPort {
				// Initialize clocks to 0
				inputReads.WriteString(fmt.Sprintf("        %s = 0;\n", portName))
				continue
			}

			inputCount++
			// Make sure we're using just the clean port name with no extra info
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
				inputReads.WriteString(fmt.Sprintf("status = $sscanf(line, \"%%h\", %s);\n", portName))
			} else {
				inputReads.WriteString(fmt.Sprintf("status = $sscanf(line, \"%%b\", %s);\n", portName))
			}

			inputReads.WriteString("        $fclose(fd);\n")
		}
	}

	// Generate clock toggling code if we have clock ports
	if len(clockPorts) > 0 {
		inputReads.WriteString("\n        // Toggle clocks for several cycles\n")
		inputReads.WriteString("        repeat (10) begin\n")

		for _, clockPort := range clockPorts {
			inputReads.WriteString(fmt.Sprintf("            %s = 0;\n", clockPort))
		}
		inputReads.WriteString("            #5;\n")

		for _, clockPort := range clockPorts {
			inputReads.WriteString(fmt.Sprintf("            %s = 1;\n", clockPort))
		}
		inputReads.WriteString("            #5;\n")

		inputReads.WriteString("        end\n")
	} else {
		// If no clock ports, just add a delay
		inputReads.WriteString("\n        // Allow module to process\n")
		inputReads.WriteString("        #10;\n")
	}

	// Generate reset toggle code if a reset signal was found
	var resetToggle strings.Builder
	if resetPort != "" {
		resetToggle.WriteString(fmt.Sprintf("        // Toggle reset signal %s\n", resetPort))
		if isActiveHigh {
			resetToggle.WriteString(fmt.Sprintf("        %s = 1; // Assert reset (active high)\n", resetPort))
			resetToggle.WriteString("        #10;\n")
			resetToggle.WriteString(fmt.Sprintf("        %s = 0; // De-assert reset\n", resetPort))
		} else {
			resetToggle.WriteString(fmt.Sprintf("        %s = 0; // Assert reset (active low)\n", resetPort))
			resetToggle.WriteString("        #10;\n")
			resetToggle.WriteString(fmt.Sprintf("        %s = 1; // De-assert reset\n", resetPort))
		}
		resetToggle.WriteString("        #10;\n")
	}

	// Generate output file writing code
	var outputWrites strings.Builder
	var outputCount int

	for _, port := range g.module.Ports {
		if port.Direction == verilog.OUTPUT {
			outputCount++
			// Make sure we're using just the clean port name with no extra info
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

	// Include the mocked module file
	includeDirective := fmt.Sprintf("`include \"%s.sv\"", g.module.Name)

	// Apply the generated code to the template
	testbench := fmt.Sprintf(svTestbenchTemplate,
		includeDirective, // Add include directive here
		declarations.String(),
		moduleInst.String(),
		inputCount,
		inputReads.String(),
		resetToggle.String(),
		outputCount,
		outputWrites.String())

	// No need to include the mock_enums.sv file since the definitions are now in the mocked file

	return utils.WriteFileContent(filepath.Join(utils.TMP_DIR, "testbench.sv"), testbench)
}

// GenerateCppTestbench creates the C++ testbench for Verilator
func (g *Generator) GenerateCppTestbench() error {
	// Generate input reading code
	var inputDecls strings.Builder
	var inputReads strings.Builder
	var inputApply strings.Builder

	for _, port := range g.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			// Make sure we're using just the clean port name with no extra info
			portName := strings.TrimSpace(port.Name)
			fileName := fmt.Sprintf("input_%s.hex", portName)

			// Add variable declaration
			if port.Width > 1 {
				inputDecls.WriteString(fmt.Sprintf("    uint%d_t %s;\n",
					nextPowerOfTwo(port.Width), portName))
			} else {
				inputDecls.WriteString(fmt.Sprintf("    uint8_t %s;\n", portName))
			}

			// Add file reading
			inputReads.WriteString(fmt.Sprintf(`    std::ifstream %s_file("%s/%s");
    if (!%s_file.is_open()) {
        std::cerr << "Error opening file: %s" << std::endl;
        delete dut;
        return 1;
    }
`, portName, utils.TMP_DIR, fileName, portName, fileName))

			// Add value parsing
			if port.Width > 1 {
				inputReads.WriteString(fmt.Sprintf("    %s_file >> std::hex >> %s;\n",
					portName, portName))
			} else {
				inputReads.WriteString(fmt.Sprintf(`    char %s_val;
    %s_file >> %s_val;
    %s = (%s_val == '1' ? 1 : 0);
`, portName, portName, portName, portName, portName))
			}

			// Apply inputs to the DUT
			inputApply.WriteString(fmt.Sprintf("    dut->%s = %s;\n", portName, portName))
		}
	}

	// Generate clock handling code
	var clockHandling strings.Builder
	var hasClock bool
	var hasReset bool
	var resetName string
	var resetActiveHigh bool

	// First identify any reset signal
	for _, port := range g.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			portName := strings.TrimSpace(port.Name)
			portNameLower := strings.ToLower(portName)

			// Check for reset signals
			if strings.Contains(portNameLower, "rst") || strings.Contains(portNameLower, "reset") {
				hasReset = true
				resetName = portName

				// Determine if active high or low (default to active high if unclear)
				resetActiveHigh = !(strings.HasSuffix(portNameLower, "_n") ||
					strings.HasSuffix(portNameLower, "_ni") ||
					strings.HasSuffix(portNameLower, "_l"))
				break
			}
		}
	}

	// Add reset toggle code after inputs have been applied
	if hasReset {
		clockHandling.WriteString("\n    // Toggle reset after inputs are applied\n")
		if resetActiveHigh {
			clockHandling.WriteString(fmt.Sprintf("    dut->%s = 1; // Assert reset (active high)\n", resetName))
		} else {
			clockHandling.WriteString(fmt.Sprintf("    dut->%s = 0; // Assert reset (active low)\n", resetName))
		}
		clockHandling.WriteString("    dut->eval();\n")
		clockHandling.WriteString("    contextp->timeInc(10);\n")

		if resetActiveHigh {
			clockHandling.WriteString(fmt.Sprintf("    dut->%s = 0; // De-assert reset\n", resetName))
		} else {
			clockHandling.WriteString(fmt.Sprintf("    dut->%s = 1; // De-assert reset\n", resetName))
		}
		clockHandling.WriteString("    dut->eval();\n")
		clockHandling.WriteString("    contextp->timeInc(10);\n")
	}

	// Add clock toggling after reset
	for _, port := range g.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			portName := strings.TrimSpace(port.Name)
			if strings.Contains(strings.ToLower(portName), "clk") ||
				strings.Contains(strings.ToLower(portName), "clock") {
				hasClock = true
				clockHandling.WriteString(fmt.Sprintf("\n    // Clock toggling for %s\n", portName))
				clockHandling.WriteString(fmt.Sprintf("    dut->%s = 0;\n", portName))
				clockHandling.WriteString("    for (int cycle = 0; cycle < 10; cycle++) {\n")
				clockHandling.WriteString(fmt.Sprintf("        dut->%s = 0;\n", portName))
				clockHandling.WriteString("        dut->eval();\n")
				clockHandling.WriteString("        contextp->timeInc(5);\n")
				clockHandling.WriteString(fmt.Sprintf("        dut->%s = 1;\n", portName))
				clockHandling.WriteString("        dut->eval();\n")
				clockHandling.WriteString("        contextp->timeInc(5);\n")
				clockHandling.WriteString("    }\n")
			}
		}
	}

	// If no clock was found, still add a basic eval
	if !hasClock {
		clockHandling.WriteString("    // No clock found, just evaluate once\n")
		clockHandling.WriteString("    dut->eval();\n")
	}

	// Generate output writing code
	var outputWrites strings.Builder

	for _, port := range g.module.Ports {
		if port.Direction == verilog.OUTPUT {
			// Make sure we're using just the clean port name with no extra info
			portName := strings.TrimSpace(port.Name)
			fileName := fmt.Sprintf("output_%s.hex", portName)

			outputWrites.WriteString(fmt.Sprintf(`    std::ofstream %s_file("%s/%s");
    if (!%s_file.is_open()) {
        std::cerr << "Error opening output file: %s" << std::endl;
        delete dut;
        return 1;
    }
`, portName, utils.TMP_DIR, fileName, portName, fileName))

			if port.Width > 1 {
				outputWrites.WriteString(fmt.Sprintf("    %s_file << std::hex << dut->%s;\n",
					portName, portName))
			} else {
				outputWrites.WriteString(fmt.Sprintf("    %s_file << (dut->%s ? '1' : '0');\n",
					portName, portName))
			}

			outputWrites.WriteString(fmt.Sprintf("    %s_file.close();\n", portName))
		}
	}

	// Apply the generated code to the template
	testbench := fmt.Sprintf(cppTestbenchTemplate,
		g.module.Name,
		g.module.Name,
		g.module.Name,
		inputDecls.String(),
		inputReads.String(),
		inputApply.String(),
		clockHandling.String(),
		outputWrites.String())

	return utils.WriteFileContent(filepath.Join(utils.TMP_DIR, "testbench.cpp"), testbench)
}

// Helper function to find the next power of two
func nextPowerOfTwo(n int) int {
	if n <= 8 {
		return 8
	} else if n <= 16 {
		return 16
	} else if n <= 32 {
		return 32
	} else if n <= 64 {
		return 64
	}
	return 128 // Cap at 128-bit for extremely wide signals
}
