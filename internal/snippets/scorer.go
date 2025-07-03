package snippets

import (
	"errors"
	"fmt"
	"path/filepath"

	"github.com/toby-bro/pfuzz/internal/simulator"
	"github.com/toby-bro/pfuzz/internal/synth"
	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

// ScoreAllSnippets evaluates all snippets against available simulators and synthesizers
func ScoreAllSnippets(verbose int) error {
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
		return errors.New("no simulators or synthesizers available for scoring")
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

	// Score the module that has the same name as the file.
	moduleName := filepath.Base(snippetFilePath)
	if moduleName == "top" {
		moduleName = "topi"
	}

	if module := verilogFile.Modules[moduleName]; module == nil {
		return fmt.Errorf("module %s not found in snippet file %s", moduleName, snippetFilePath)
	} else {
		score := &SnippetScore{
			NumSimulators:    len(availableSimulators),
			NumSynthesizers:  len(availableSynthesizers),
			SimulatorScore:   0,
			SynthesizerScore: 0,
			MaximalScore:     2*len(availableSimulators) + len(availableSynthesizers),
			ReachedScore:     0,
		}
		if score.MaximalScore == 0 {
			return fmt.Errorf("no simulators or synthesizers available for scoring module %s", moduleName)
		}

		/*
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
		*/
	}

	return nil
}
