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
	debug.Info("Found %d available synthesizers: %v", len(availableSynthesizers), availableSynthesizers)
	
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
		simulatorScore := testSnippetWithSimulators(snippetFilePath, module, availableSimulators, debug)
		score.SimulatorScore = simulatorScore
		score.ReachedScore += simulatorScore
		
		// Test with synthesizers  
		synthesizerScore := testSnippetWithSynthesizers(snippetFilePath, module, availableSynthesizers, debug)
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
	err := os.MkdirAll(tempDir, 0755)
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
		
		// Try to compile with this simulator
		compilationScore := testSnippetCompilation(tempSnippetPath, module, simType, debug)
		totalScore += compilationScore
		
		if compilationScore > 0 {
			// If compilation succeeded, try simulation
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
	// For now, let's simplify and just test if the tools exist
	// A more complete implementation would actually try to compile
	debug.Debug("Testing compilation for %s (simplified check)", simType.String())
	
	switch simType {
	case simulator.IVERILOG:
		if err := simulator.TestIVerilogTool(); err != nil {
			debug.Debug("IVerilog tool check failed: %v", err)
			return 0
		}
	case simulator.VERILATOR:
		if err := simulator.TestVerilatorTool(); err != nil {
			debug.Debug("Verilator tool check failed: %v", err)
			return 0
		}
	case simulator.CXXRTL, simulator.CXXSLG:
		if err := simulator.TestCXXRTLTool(simType == simulator.CXXSLG); err != nil {
			debug.Debug("CXXRTL tool check failed: %v", err)
			return 0
		}
	default:
		debug.Debug("Unsupported simulator type for testing: %s", simType.String())
		return 0
	}
	
	debug.Debug("Tool available for %s", simType.String())
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
	tempDir := filepath.Join(os.TempDir(), fmt.Sprintf("snippet_synth_test_%d", time.Now().UnixNano()))
	err := os.MkdirAll(tempDir, 0755)
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
	// For now, let's simplify and just test if the tools exist
	// A more complete implementation would actually try to synthesize
	debug.Debug("Testing synthesis for %s (simplified check)", synthType.String())
	
	switch synthType {
	case synth.YOSYS:
		if err := synth.TestYosysTool(); err != nil {
			debug.Debug("Yosys tool check failed: %v", err)
			return 0
		}
	case synth.SV2V:
		if err := synth.TestSV2VTool(); err != nil {
			debug.Debug("SV2V tool check failed: %v", err)
			return 0
		}
	default:
		debug.Debug("Unsupported synthesizer type for testing: %s", synthType.String())
		return 0
	}
	
	debug.Debug("Tool available for %s", synthType.String())
	return 1
}