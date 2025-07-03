package fuzz

import (
	"context"
	"fmt"
	"path/filepath"
	"strings"
	"time"

	"github.com/toby-bro/pfuzz/internal/simulator"
	"github.com/toby-bro/pfuzz/internal/synth"
	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

// SnippetScoreResult holds the result for a single snippet file
// which simulators/synthesizers succeeded or failed
type SnippetScoreResult struct {
	FileName           string
	ModuleName         string
	SimulatorResults   map[simulator.Type]error
	SynthesizerResults map[synth.Type]error
}

// Detailed result for a single tool
// For simulators: Compile and Simulate
// For synthesizers: Synthesize
type SimulatorScoreDetail struct {
	CompileOk   bool
	SimulateOk  bool
	CompileErr  error
	SimulateErr error
}

type SynthesizerScoreDetail struct {
	SynthesizeOk  bool
	SynthesizeErr error
}

// ScoreSnippetsWithDetails runs each snippet file through the actual compile/sim/synth steps
// and returns detailed results for each snippet (success/failure per tool and step)
func ScoreSnippetsWithDetails(
	verbose int,
	findSnippetFiles func() ([]string, error),
) ([]SnippetScoreResult, error) {
	debug := utils.NewDebugLogger(verbose)
	results := []SnippetScoreResult{}

	// Find all snippet files
	snippetFiles, err := findSnippetFiles()
	if err != nil {
		return nil, fmt.Errorf("failed to find snippet files: %v", err)
	}

	for _, snippetFile := range snippetFiles {
		moduleNameWithExt := filepath.Base(snippetFile)
		moduleName := strings.TrimSuffix(moduleNameWithExt, filepath.Ext(moduleNameWithExt))
		if moduleName == "top" {
			moduleName = "topi"
		}

		// Parse the snippet file
		fileContent, err := utils.ReadFileContent(snippetFile)
		if err != nil {
			debug.Warn("Skipping %s: %v", snippetFile, err)
			continue
		}
		vf, err := verilog.ParseVerilog(fileContent, verbose)
		if err != nil || vf == nil {
			debug.Warn("Skipping %s: failed to parse: %v", snippetFile, err)
			continue
		}
		var mod *verilog.Module
		if len(vf.Modules) == 1 {
			for _, m := range vf.Modules {
				mod = m
				break
			}
			moduleName = mod.Name
		} else {
			mod = vf.Modules[moduleName]
		}
		if mod == nil {
			debug.Warn("Skipping %s: module %s not found", snippetFile, moduleName)
			continue
		}

		// Simulators
		availableSimulators := simulator.TestAvailableSimulators(debug)
		// Synthesizers
		availableSynthesizers := synth.TestAvailableSynthesizers(debug)

		result := SnippetScoreResult{
			FileName:           snippetFile,
			ModuleName:         moduleName,
			SimulatorResults:   make(map[simulator.Type]error),
			SynthesizerResults: make(map[synth.Type]error),
		}

		// Score each simulator
		for _, simType := range availableSimulators {
			var compileErr, simErr error
			ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
			switch simType {
			case simulator.IVERILOG:
				sim := simulator.NewIVerilogSimulator("/tmp", snippetFile, verbose)
				compileErr = sim.Compile(ctx)
				if compileErr == nil {
					simErr = sim.RunTest(ctx, "/tmp", map[string]string{})
				}
			case simulator.VERILATOR:
				sim := simulator.NewVerilatorSimulator("/tmp", vf, moduleName, false, verbose)
				if sim == nil {
					debug.Error(
						"VerilatorSimulator could not be created for module %s",
						moduleName,
					)
				} else {
					compileErr = sim.Compile(ctx)
					if compileErr == nil {
						simErr = sim.RunTest(ctx, "/tmp", map[string]string{})
					}
				}
			case simulator.CXXRTL:
				sim := simulator.NewCXXRTLSimulator(
					"/tmp",
					snippetFile,
					moduleName,
					"",
					false,
					verbose,
				)
				compileErr = sim.Compile(ctx)
				if compileErr == nil {
					simErr = sim.RunTest(ctx, "/tmp", nil)
				}
			case simulator.CXXSLG:
				sim := simulator.NewCXXRTLSimulator(
					"/tmp",
					snippetFile,
					moduleName,
					"",
					true,
					verbose,
				)
				compileErr = sim.Compile(ctx)
				if compileErr == nil {
					simErr = sim.RunTest(ctx, "/tmp", nil)
				}
			default:
				compileErr = fmt.Errorf("simulator %v not supported in scoring", simType)
			}
			cancel()
			if compileErr != nil {
				result.SimulatorResults[simType] = compileErr
			} else if simErr != nil {
				result.SimulatorResults[simType] = simErr
			} else {
				result.SimulatorResults[simType] = nil
			}
		}

		// Score each synthesizer
		for _, synType := range availableSynthesizers {
			var synthErr error
			switch synType {
			case synth.YOSYS:
				synthErr = synth.YosysSynth(moduleName, snippetFile, nil)
				utils.DeleteFile(utils.AddSuffixToPath(snippetFile, "yosys"))
			case synth.SV2V:
				synthErr = synth.TransformSV2V(moduleName, snippetFile)
				utils.DeleteFile(
					utils.ChangeExtension(utils.AddSuffixToPath(snippetFile, "sv2v"), "v"),
				)
			default:
				synthErr = fmt.Errorf("synthesizer %v not supported in scoring", synType)
			}
			result.SynthesizerResults[synType] = synthErr
		}

		results = append(results, result)
	}
	return results, nil
}
