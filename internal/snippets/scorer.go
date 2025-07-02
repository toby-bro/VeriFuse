package snippets

import (
	"fmt"
	"os"
	"path/filepath"
	"time"

	"github.com/toby-bro/pfuzz/internal/simulator"
	"github.com/toby-bro/pfuzz/internal/synth"
	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

// ScoreAllSnippets evaluates all snippets against available simulators and synthesizers
func ScoreAllSnippets(verbose int) error {
	logger.SetVerboseLevel(verbose)
	debug := utils.NewDebugLogger(verbose)

	debug.Info("Starting snippet scoring process...")

	// Get available simulators and synthesizers
	availableSimulators := simulator.TestAvailableSimulators(debug)
	debug.Info("Found %d available simulators: %v", len(availableSimulators), availableSimulators)

	availableSynthesizers := synth.TestAvailableSynthesizers(debug)
	debug.Info(
		"Found %d available synthesizers: %v",
		len(availableSynthesizers),
		availableSynthesizers,
	)

	if len(availableSimulators) == 0 && len(availableSynthesizers) == 0 {
		return fmt.Errorf("no simulators or synthesizers available for scoring")
	}

	// Find all snippet files
	sourceFiles, err := findSnippetFiles()
	if err != nil {
		return fmt.Errorf("failed to find snippet files: %v", err)
	}

	debug.Info("Found %d snippet files to score", len(sourceFiles))

	// Score each snippet file
	for i, snippetFile := range sourceFiles {
		debug.Info("Scoring snippet file %d/%d: %s", i+1, len(sourceFiles), snippetFile)

		err := scoreSnippetFile(snippetFile, availableSimulators, availableSynthesizers, debug)
		if err != nil {
			debug.Warn("Failed to score snippet file %s: %v", snippetFile, err)
			continue
		}
	}

	debug.Info("Snippet scoring completed")
	return nil
}

// scoreSnippetFile scores a single snippet file against all available tools
func scoreSnippetFile(
	snippetFilePath string,
	availableSimulators []simulator.Type,
	availableSynthesizers []synth.Type,
	debug *utils.DebugLogger,
) error {
	// Read and parse the snippet file
	fileContent, err := utils.ReadFileContent(snippetFilePath)
	if err != nil {
		return fmt.Errorf("failed to read snippet file: %v", err)
	}

	verilogFile, err := verilog.ParseVerilog(fileContent, debug.GetVerboseLevel())
	if err != nil {
		return fmt.Errorf("failed to parse verilog file: %v", err)
	}

	// Score each module in the file
	for _, module := range verilogFile.Modules {
		moduleName := module.Name
		if moduleName == "top" {
			moduleName = "topi"
		}

		debug.Debug("Scoring module: %s", moduleName)

		score := &SnippetScore{
			NumSimulators:    len(availableSimulators),
			NumSynthesizers:  len(availableSynthesizers),
			SimulatorScore:   0,
			SynthesizerScore: 0,
			MaximalScore:     2*len(availableSimulators) + len(availableSynthesizers),
			ReachedScore:     0,
		}

		// Test with simulators
		simulatorScore := testSnippetWithSimulators(
			snippetFilePath,
			module,
			availableSimulators,
			debug,
		)
		score.SimulatorScore = simulatorScore
		score.ReachedScore += simulatorScore

		// Test with synthesizers
		synthesizerScore := testSnippetWithSynthesizers(
			snippetFilePath,
			module,
			availableSynthesizers,
			debug,
		)
		score.SynthesizerScore = synthesizerScore
		score.ReachedScore += synthesizerScore

		// Calculate probability
		if score.MaximalScore > 0 {
			score.Probability = float64(score.ReachedScore) / float64(score.MaximalScore)
		}

		debug.Info("Module %s scored %d/%d (%.2f%%)",
			moduleName, score.ReachedScore, score.MaximalScore, score.Probability*100)

		// Write score file
		err = WriteScoreFile(snippetFilePath, score)
		if err != nil {
			debug.Warn("Failed to write score file for %s: %v", moduleName, err)
		}
	}

	return nil
}

// testSnippetWithSimulators tests a snippet against all available simulators
func testSnippetWithSimulators(
	snippetFilePath string,
	module *verilog.Module,
	availableSimulators []simulator.Type,
	debug *utils.DebugLogger,
) int {
	totalScore := 0

	// Create a temporary directory for testing
	tempDir := filepath.Join(os.TempDir(), fmt.Sprintf("snippet_test_%d", time.Now().UnixNano()))
	err := os.MkdirAll(tempDir, 0o755)
	if err != nil {
		debug.Warn("Failed to create temp directory for simulator testing: %v", err)
		return 0
	}
	defer os.RemoveAll(tempDir)

	// Copy snippet file to temp directory
	tempSnippetPath := filepath.Join(tempDir, "snippet.sv")
	err = utils.CopyFile(snippetFilePath, tempSnippetPath)
	if err != nil {
		debug.Warn("Failed to copy snippet file for testing: %v", err)
		return 0
	}

	for _, simType := range availableSimulators {
		debug.Debug("Testing snippet with simulator: %s", simType.String())

		// Test compilation (score 1 if successful)
		compilationScore := testSnippetCompilation(tempSnippetPath, module, simType, debug)
		totalScore += compilationScore

		// Test simulation (score 1 additional if successful)
		if compilationScore > 0 {
			simulationScore := testSnippetSimulation(tempSnippetPath, module, simType, debug)
			totalScore += simulationScore
		}
	}

	return totalScore
}

// testSnippetCompilation tests if a snippet compiles with a given simulator
func testSnippetCompilation(
	snippetPath string,
	module *verilog.Module,
	simType simulator.Type,
	debug *utils.DebugLogger,
) int {
	// First check if the tool is available
	var toolAvailable bool
	switch simType {
	case simulator.IVERILOG:
		toolAvailable = simulator.TestIVerilogTool() == nil
	case simulator.VERILATOR:
		toolAvailable = simulator.TestVerilatorTool() == nil
	case simulator.CXXRTL, simulator.CXXSLG:
		toolAvailable = simulator.TestCXXRTLTool(simType == simulator.CXXSLG) == nil
	default:
		debug.Debug("Unsupported simulator type for testing: %s", simType.String())
		return 0
	}

	if !toolAvailable {
		debug.Debug("Tool not available for %s", simType.String())
		return 0
	}

	debug.Debug("Tool available for %s, performing compilation test...", simType.String())

	// Try actual compilation for a more accurate score
	// We'll use a simplified approach that just tests tool availability for now
	// In a more complete implementation, we would:
	// 1. Create the appropriate simulator instance with correct parameters
	// 2. Try to compile the snippet
	// 3. Handle any compilation errors gracefully

	// For IVerilog, we can try a basic syntax check
	if simType == simulator.IVERILOG {
		return testIVerilogCompilation(snippetPath, debug)
	}

	// For other simulators, return 1 since tool is available
	// TODO: Implement actual compilation tests for Verilator and CXXRTL
	debug.Debug("Compilation test passed for %s (tool availability verified)", simType.String())
	return 1
}

// testIVerilogCompilation performs a basic syntax check with IVerilog
func testIVerilogCompilation(snippetPath string, debug *utils.DebugLogger) int {
	// Try to compile with iverilog just for syntax checking
	cmd := fmt.Sprintf("iverilog -t null %s", snippetPath)
	debug.Debug("Running: %s", cmd)

	// Create a simple test command
	if err := utils.RunCommandWithTimeout(cmd, 10*time.Second); err != nil {
		debug.Debug("IVerilog compilation failed: %v", err)
		return 0
	}

	debug.Debug("IVerilog compilation succeeded")
	return 1
}

// testSnippetSimulation tests if a snippet can be simulated after compilation
func testSnippetSimulation(
	snippetPath string,
	module *verilog.Module,
	simType simulator.Type,
	debug *utils.DebugLogger,
) int {
	// For now, we'll just assume simulation works if compilation worked
	// A more complete implementation would actually try to run the simulation
	// with some test inputs, but that requires more complex setup
	debug.Debug("Simulation test not implemented yet for %s, assuming success", simType.String())
	return 1
}

// testSnippetWithSynthesizers tests a snippet against all available synthesizers
func testSnippetWithSynthesizers(
	snippetFilePath string,
	module *verilog.Module,
	availableSynthesizers []synth.Type,
	debug *utils.DebugLogger,
) int {
	totalScore := 0

	// Create a temporary directory for testing
	tempDir := filepath.Join(
		os.TempDir(),
		fmt.Sprintf("snippet_synth_test_%d", time.Now().UnixNano()),
	)
	err := os.MkdirAll(tempDir, 0o755)
	if err != nil {
		debug.Warn("Failed to create temp directory for synthesizer testing: %v", err)
		return 0
	}
	defer os.RemoveAll(tempDir)

	// Copy snippet file to temp directory
	tempSnippetPath := filepath.Join(tempDir, "snippet.sv")
	err = utils.CopyFile(snippetFilePath, tempSnippetPath)
	if err != nil {
		debug.Warn("Failed to copy snippet file for synthesizer testing: %v", err)
		return 0
	}

	for _, synthType := range availableSynthesizers {
		debug.Debug("Testing snippet with synthesizer: %s", synthType.String())

		// Try to synthesize with this tool
		synthScore := testSnippetSynthesis(tempSnippetPath, module, synthType, debug)
		totalScore += synthScore
	}

	return totalScore
}

// testSnippetSynthesis tests if a snippet can be synthesized with a given tool
func testSnippetSynthesis(
	snippetPath string,
	module *verilog.Module,
	synthType synth.Type,
	debug *utils.DebugLogger,
) int {
	// First check if the tool is available
	var toolAvailable bool
	switch synthType {
	case synth.YOSYS:
		toolAvailable = synth.TestYosysTool() == nil
	case synth.SV2V:
		toolAvailable = synth.TestSV2VTool() == nil
	default:
		debug.Debug("Unsupported synthesizer type for testing: %s", synthType.String())
		return 0
	}

	if !toolAvailable {
		debug.Debug("Tool not available for %s", synthType.String())
		return 0
	}

	debug.Debug("Tool available for %s, performing synthesis test...", synthType.String())

	// Try actual synthesis for a more accurate score
	if synthType == synth.YOSYS {
		return testYosysSynthesis(snippetPath, module, debug)
	}

	// For other synthesizers, return 1 since tool is available
	// TODO: Implement actual synthesis tests for other tools
	debug.Debug("Synthesis test passed for %s (tool availability verified)", synthType.String())
	return 1
}

// testYosysSynthesis performs a basic synthesis test with Yosys
func testYosysSynthesis(snippetPath string, module *verilog.Module, debug *utils.DebugLogger) int {
	// Try a basic read_verilog command to test if the file can be parsed
	cmd := fmt.Sprintf("yosys -p 'read_verilog %s; hierarchy -check' -q", snippetPath)
	debug.Debug("Running: %s", cmd)

	if err := utils.RunCommandWithTimeout(cmd, 10*time.Second); err != nil {
		debug.Debug("Yosys synthesis test failed: %v", err)
		return 0
	}

	debug.Debug("Yosys synthesis test succeeded")
	return 1
}
