package fuzz

import (
	"bytes"
	"context"
	"fmt"
	"os"
	"os/exec" // Added for running yosys-config
	"path/filepath"
	"strings"
	"time"

	"github.com/toby-bro/pfuzz/internal/simulator"
	"github.com/toby-bro/pfuzz/internal/testgen"
	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

// SimInstance holds a name and a compiled simulator interface.
type SimInstance struct {
	Name      string
	Simulator simulator.Simulator
	Prefix    string
}

func (sch *Scheduler) setupWorker(workerID string) (string, func(), error) {
	workerDir := filepath.Join(utils.TMP_DIR, workerID)
	sch.debug.Debug("[%s] Creating worker directory at %s", workerID, workerDir)
	if err := os.MkdirAll(workerDir, 0o755); err != nil {
		sch.debug.Error("[%s] Failed to create worker directory %s: %v", workerID, workerDir, err)
		return "", nil, err
	}
	cleanup := func() {
		if err := os.RemoveAll(workerDir); err != nil {
			sch.debug.Warn("Failed to clean up worker directory %s: %v", workerDir, err)
		}
		sch.debug.Debug("Cleaned up worker directory: %s", workerDir)
	}
	return workerDir, cleanup, nil
}

func (sch *Scheduler) copyWorkerFiles(workerID, workerDir, verilogFileName string) error {
	srcPath := filepath.Join(utils.TMP_DIR, verilogFileName)
	dstPath := filepath.Join(workerDir, verilogFileName)
	sch.debug.Debug(
		"[%s] Copying Verilog source file `%s` to `%s`",
		workerID,
		srcPath,
		dstPath,
	)
	if _, err := os.Stat(srcPath); os.IsNotExist(err) {
		return fmt.Errorf("[%s] Source Verilog file %s does not exist", workerID, srcPath)
	}
	if err := utils.CopyFile(srcPath, dstPath); err != nil {
		return fmt.Errorf("failed to copy %s to worker directory: %w", verilogFileName, err)
	}
	if fi, err := os.Stat(dstPath); err != nil || fi.Size() == 0 {
		fileSize := int64(0)
		if fi != nil {
			fileSize = fi.Size()
		}
		return fmt.Errorf("[%s] Verilog file %s not copied correctly, size: %d, error: %v",
			workerID, dstPath, fileSize, err)
	}
	sch.debug.Debug("[%s] Successfully copied %s", workerID, verilogFileName)
	return nil
}

// performWorkerAttempt tries to set up and run tests for one worker attempt.
// It returns true if the setup was successful and test processing started, along with any error from setup.
// If setup was successful, the error returned is nil.
// If setup failed, it returns false and the setup error.
func (sch *Scheduler) performWorkerAttempt(
	ctx context.Context,
	workerID string,
	testCases <-chan int,
	workerModule *verilog.Module,
	strategy Strategy,
) (setupSuccessful bool, err error) {
	workerDir, cleanupFunc, setupErr := sch.setupWorker(workerID)
	if setupErr != nil {
		return false, fmt.Errorf("worker setup failed for %s: %w", workerID, setupErr)
	}

	attemptCompletelySuccessful := false
	defer func() {
		if cleanupFunc != nil {
			if (sch.verbose > 2 && !attemptCompletelySuccessful) || sch.verbose > 3 ||
				sch.keepFiles {
				sch.debug.Debug(
					"[%s] Preserving worker directory %s (verbose = %d). Attempt success: %t",
					workerID,
					workerDir,
					sch.verbose,
					attemptCompletelySuccessful,
				)
			} else {
				sch.debug.Debug("[%s] Cleaning up worker directory %s. Attempt success: %t", workerID, workerDir, attemptCompletelySuccessful)
				cleanupFunc()
			}
		}
	}()

	if err := sch.copyWorkerFiles(workerID, workerDir, sch.svFile.Name); err != nil {
		return false, fmt.Errorf("failed to copy files for worker %s: %w", workerID, err)
	}

	workerVerilogPath := filepath.Join(workerDir, sch.svFile.Name)
	var svFile *verilog.VerilogFile
	if sch.operation == OpMutate {
		sch.debug.Debug("[%s] Attempting mutation on %s", workerID, workerVerilogPath)
		if svFile, err = MutateFile(sch.svFile, workerVerilogPath, sch.verbose); err != nil {
			return false, fmt.Errorf("[%s] mutation failed: %w", workerID, err)
		}
		sch.debug.Debug("[%s] Mutation applied. Proceeding.", workerID)
	} else {
		sch.debug.Debug("[%s] Mutation not requested. Proceeding with original file.", workerID)
		fileContent, err := utils.ReadFileContent(workerVerilogPath)
		if err != nil {
			return false, fmt.Errorf("[%s] failed to read Verilog file: %w", workerID, err)
		}
		svFile, err = verilog.ParseVerilog(fileContent, sch.verbose)
		if err != nil {
			return false, fmt.Errorf("[%s] failed to parse Verilog file: %w", workerID, err)
		}
		svFile.Name = sch.svFile.Name // Ensure basename is correct
	}

	if err = simulator.TransformSVToV(workerModule.Name, workerVerilogPath, svFile.Name); err != nil {
		sch.debug.Warn(
			"[%s] Failed to transform SystemVerilog to Verilog for module %s: %v",
			workerID,
			workerModule.Name,
			err,
		)
	}

	sch.debug.Debug(
		"[%s] Parsed %d modules from file %s (path: %s).",
		workerID,
		len(svFile.Modules),
		svFile.Name,
		workerVerilogPath,
	)

	// Ensure workerModule is from the current svFile
	currentWorkerModule, ok := svFile.Modules[workerModule.Name]
	if !ok {
		return false, fmt.Errorf(
			"[%s] worker module %s not found in parsed file %s for current attempt",
			workerID,
			workerModule.Name,
			svFile.Name,
		)
	}

	sch.debug.Debug(
		"[%s] Generating testbenches for module %s in %s",
		workerID,
		currentWorkerModule.Name,
		workerDir,
	)
	gen := testgen.NewGenerator(
		currentWorkerModule,
		svFile.Name,
		svFile,
	) // Use current (mutated) svFile.Name
	if err := gen.GenerateSVTestbench(workerDir); err != nil { // Generates testbench.sv in workerDir
		return false, fmt.Errorf(
			"[%s] failed to generate SystemVerilog testbenches: %w",
			workerID,
			err,
		)
	}

	// Check if CXXRTL is intended to be used and generate its testbench
	for _, sim_dir := range []string{"cxxrtl_sim", "cxxrtl_slang_sim", "cxxrtl_sim_sv2v", "cxxrtl_slang_sim_sv2v"} {
		cxxrtlSimDir := filepath.Join(workerDir, sim_dir)
		if err := os.MkdirAll(cxxrtlSimDir, 0o755); err != nil {
			return false, fmt.Errorf("[%s] failed to create cxxrtl_sim dir: %w", workerID, err)
		}
		if err := gen.GenerateCXXRTLTestbench(cxxrtlSimDir); err != nil { // Pass cxxrtlSimDir
			return false, fmt.Errorf("[%s] failed to generate CXXRTL testbench: %w", workerID, err)
		}
	}

	sch.debug.Debug("[%s] Testbenches generated.", workerID)

	sims, err := sch.setupSimulators(
		ctx,
		workerID,
		workerDir,
		currentWorkerModule.Name,
		svFile,
	) // Pass current svFile
	if err != nil {
		// If setupSimulators returns an error, it means no simulators could be compiled.
		// Specific compilation errors for individual simulators are logged within setupSimulators.
		// We might want to call handleGenericCompilationFailure here if *all* fail.
		return false, fmt.Errorf("simulator setup failed for worker %s: %w", workerID, err)
	}

	sch.debug.Debug(
		"[%s] Simulators set up successfully: %d simulators ready.",
		workerID,
		len(sims),
	)
	sch.debug.Debug(
		"[%s] Starting test case processing for module %s. Strategy: %s",
		workerID,
		currentWorkerModule.Name,
		strategy.Name(),
	)

	errorList := sch.processTestCases(
		ctx,
		workerID,
		workerDir, // This is the base directory for the worker attempt
		sims,      // Pass the slice of SimInstance
		currentWorkerModule,
		testCases,
		strategy,
	)
	if len(errorList) > 0 {
		var errBuilder strings.Builder
		for i, e := range errorList {
			if i > 0 {
				errBuilder.WriteString("; ")
			}
			errBuilder.WriteString(e.Error())
		}
		return false, fmt.Errorf(
			"[%s] test case processing failed with %d errors: %s",
			workerID,
			len(errorList),
			errBuilder.String(),
		)
	}
	attemptCompletelySuccessful = true // Mark as successful for cleanup logic
	return true, nil
}

func (sch *Scheduler) setupSimulators(
	ctx context.Context,
	workerID, baseWorkerDir, workerModuleName string,
	svFileToCompile *verilog.VerilogFile, // svFileToCompile is the (potentially mutated) one
) ([]*SimInstance, error) {
	sch.debug.Debug(
		"[%s] Setting up simulators for module %s in %s",
		workerID,
		workerModuleName,
		baseWorkerDir,
	)
	var compiledSims []*SimInstance
	var setupErrors []string

	// 1. Icarus Verilog
	ivWorkDir := baseWorkerDir // Icarus compiles in the base worker dir
	ivsim := simulator.NewIVerilogSimulator(filepath.Join(ivWorkDir, "icarus"), sch.verbose)
	sch.debug.Debug("[%s] Compiling IVerilog simulator in %s", workerID, ivWorkDir)

	// Create compilation context with timeout
	compileCtx, compileCancel := context.WithTimeout(ctx, sch.timeouts.CompilationTimeout)
	defer compileCancel()

	if err := ivsim.Compile(compileCtx); err != nil {
		sch.debug.Warn("[%s] Failed to compile IVerilog: %v", workerID, err)
		setupErrors = append(setupErrors, fmt.Sprintf("iverilog: %v", err))
		// sch.handleGenericCompilationFailure(workerID, workerModuleName, "iverilog", err, baseWorkerDir)
	} else {
		sch.debug.Debug("[%s] IVerilog compiled successfully.", workerID)
		compiledSims = append(compiledSims, &SimInstance{Name: "icarus", Simulator: ivsim, Prefix: "iv_"})
	}

	// 2. Verilator O0
	vlO0WorkDir := filepath.Join(baseWorkerDir, "vl_O0")
	if err := os.MkdirAll(vlO0WorkDir, 0o755); err != nil {
		sch.debug.Warn(
			"[%s] Failed to create Verilator O0 directory %s: %v",
			workerID,
			vlO0WorkDir,
			err,
		)
		setupErrors = append(setupErrors, fmt.Sprintf("verilator_O0_mkdir: %v", err))
	} else {
		vlsim0 := simulator.NewVerilatorSimulator(vlO0WorkDir, svFileToCompile, workerModuleName, false, sch.verbose)
		sch.debug.Debug("[%s] Compiling Verilator O0 simulator in %s", workerID, vlO0WorkDir)

		// Create compilation context with timeout for Verilator O0
		compileCtx0, compileCancel0 := context.WithTimeout(ctx, sch.timeouts.CompilationTimeout)
		defer compileCancel0()

		if err := vlsim0.Compile(compileCtx0); err != nil {
			sch.debug.Warn("[%s] Failed to compile Verilator O0: %v", workerID, err)
			setupErrors = append(setupErrors, fmt.Sprintf("verilator_O0: %v", err))
			// sch.handleGenericCompilationFailure(workerID, workerModuleName, "verilator_O0", err, baseWorkerDir)
		} else {
			sch.debug.Debug("[%s] Verilator O0 compiled successfully.", workerID)
			compiledSims = append(compiledSims, &SimInstance{Name: "vtor01", Simulator: vlsim0, Prefix: "vl01_"})
		}
	}

	// 3. Verilator O3
	vlO3WorkDir := filepath.Join(baseWorkerDir, "vl_O3")
	if err := os.MkdirAll(vlO3WorkDir, 0o755); err != nil {
		sch.debug.Warn(
			"[%s] Failed to create Verilator O3 directory %s: %v",
			workerID,
			vlO3WorkDir,
			err,
		)
		setupErrors = append(setupErrors, fmt.Sprintf("verilator_O3_mkdir: %v", err))
	} else {
		vlsim3 := simulator.NewVerilatorSimulator(vlO3WorkDir, svFileToCompile, workerModuleName, true, sch.verbose)
		sch.debug.Debug("[%s] Compiling Verilator O3 simulator in %s", workerID, vlO3WorkDir)

		// Create compilation context with timeout for Verilator O3
		compileCtx3, compileCancel3 := context.WithTimeout(ctx, sch.timeouts.CompilationTimeout)
		defer compileCancel3()

		if err := vlsim3.Compile(compileCtx3); err != nil {
			sch.debug.Warn("[%s] Failed to compile Verilator O3: %v", workerID, err)
			setupErrors = append(setupErrors, fmt.Sprintf("verilator_O3: %v", err))
			// sch.handleGenericCompilationFailure(workerID, workerModuleName, "verilator_O3", err, baseWorkerDir)
		} else {
			sch.debug.Debug("[%s] Verilator O3 compiled successfully.", workerID)
			compiledSims = append(compiledSims, &SimInstance{Name: "vtor31", Simulator: vlsim3, Prefix: "vl31_"})
		}
	}

	// 4. CXXRTL
	cxxrtlWorkDir := filepath.Join(
		baseWorkerDir,
		"cxxrtl_sim",
	) // Matches dir used for testbench generation
	// Ensure CXXRTL include directory is available from scheduler config
	// Attempt to use yosys-config to find the CXXRTL runtime include directory
	yosysCmd := exec.Command("yosys-config", "--datdir")
	var yosysOut bytes.Buffer
	var yosysErr bytes.Buffer
	yosysCmd.Stdout = &yosysOut
	yosysCmd.Stderr = &yosysErr

	var includeDir string

	if err := yosysCmd.Run(); err == nil {
		yosysDatDir := strings.TrimSpace(yosysOut.String())
		// Construct path based on yosys datdir and known structure for cxxrtl runtime
		potentialPath := filepath.Join(
			yosysDatDir,
			"include",
			"backends",
			"cxxrtl",
			"runtime",
		)

		if _, statErr := os.Stat(potentialPath); statErr == nil {
			includeDir = potentialPath
			sch.debug.Debug(
				"[%s] Using CXXRTL_INCLUDE_DIR (runtime) from yosys-config: %s",
				workerID,
				includeDir,
			)
		} else {
			sch.debug.Debug("[%s] yosys-config derived CXXRTL runtime path %s not found (stat error: %v). Will try defaults.", workerID, potentialPath, statErr)
		}
	} else {
		errMsg := strings.TrimSpace(yosysErr.String())
		sch.debug.Warn("[%s] 'yosys-config --datdir' command failed: %v. Stderr: '%s'. Will try default CXXRTL include paths.", workerID, err, errMsg)
	}

	// svFileToCompile.Name is the base name of the Verilog file (e.g., design.v)
	cxxrtlOriginalVerilogBaseName := svFileToCompile.Name
	cxsim := simulator.NewCXXRTLSimulator(
		cxxrtlWorkDir,
		cxxrtlOriginalVerilogBaseName,
		workerModuleName,
		includeDir,
		false, // optimized
		false, // useSlang
		sch.verbose,
	)
	sch.debug.Debug("[%s] Compiling CXXRTL simulator in %s", workerID, cxxrtlWorkDir)
	// Attempt to compile CXXRTL
	if err := os.MkdirAll(cxxrtlWorkDir, 0o755); err != nil {
		setupErrors = append(setupErrors, fmt.Sprintf("CXXRTL mkdir error: %v", err))
		sch.debug.Error(
			"[%s] Failed to create CXXRTL work directory %s: %v",
			workerID,
			cxxrtlWorkDir,
			err,
		)
	} else {
		// Create compilation context with timeout for CXXRTL
		compileCtxCXX, compileCancelCXX := context.WithTimeout(ctx, sch.timeouts.CompilationTimeout)
		defer compileCancelCXX()

		if err := cxsim.Compile(compileCtxCXX); err != nil {
			sch.debug.Warn("[%s] CXXRTL compilation failed in %s: %v", workerID, cxxrtlWorkDir, err)
			// sch.handleCompilationFailure(workerID, "CXXRTL", cxxrtlWorkDir, err, svFileToCompile.Name, workerModuleName)
			setupErrors = append(setupErrors, fmt.Sprintf("CXXRTL compile error: %v", err))
		} else {
			sch.debug.Debug("[%s] Successfully compiled CXXRTL simulator in %s.", workerID, cxxrtlWorkDir)
			compiledSims = append(compiledSims, &SimInstance{Name: "CXXRTL", Simulator: cxsim, Prefix: "cxx_vanilla_"})
		}
	}

	// 5. CXXRTL with Slang
	cxxrtlSlangWorkDir := filepath.Join(baseWorkerDir, "cxxrtl_slang_sim")
	// Ensure CXXRTL include directory is available from scheduler config (same as above)
	// includeDir is already defined
	cxxrtlSlangOriginalVerilogBaseName := svFileToCompile.Name // Use the same potentially mutated Verilog file
	cxSlangSim := simulator.NewCXXRTLSimulator(
		cxxrtlSlangWorkDir,
		cxxrtlSlangOriginalVerilogBaseName,
		workerModuleName,
		includeDir,
		false, // optimized
		true,  // useSlang
		sch.verbose,
	)
	sch.debug.Debug(
		"[%s] Compiling CXXRTL simulator with Slang in %s",
		workerID,
		cxxrtlSlangWorkDir,
	)
	// Attempt to compile CXXRTL with Slang
	if err := os.MkdirAll(cxxrtlSlangWorkDir, 0o755); err != nil {
		setupErrors = append(setupErrors, fmt.Sprintf("CXXRTL (Slang) mkdir error: %v", err))
		sch.debug.Error(
			"[%s] Failed to create CXXRTL (Slang) work directory %s: %v",
			workerID,
			cxxrtlSlangWorkDir,
			err,
		)
	} else {
		// Create compilation context with timeout for CXXRTL with Slang
		compileCtxSlang, compileCancelSlang := context.WithTimeout(ctx, sch.timeouts.CompilationTimeout)
		defer compileCancelSlang()

		if err := cxSlangSim.Compile(compileCtxSlang); err != nil {
			sch.debug.Warn("[%s] CXXRTL (Slang) compilation failed in %s: %v", workerID, cxxrtlSlangWorkDir, err)
			// sch.handleCompilationFailure(workerID, "CXXRTL_SLANG", cxxrtlSlangWorkDir, err, svFileToCompile.Name, workerModuleName)
			setupErrors = append(setupErrors, fmt.Sprintf("CXXRTL (Slang) compile error: %v", err))
		} else {
			sch.debug.Debug("[%s] Successfully compiled CXXRTL (Slang) simulator in %s.", workerID, cxxrtlSlangWorkDir)
			compiledSims = append(compiledSims, &SimInstance{Name: "CXXSLG", Simulator: cxSlangSim, Prefix: "cxx_slang_"})
		}
	}

	// Now create sv2v variants that use the transformed .v files instead of .sv files
	vFileName := strings.TrimSuffix(svFileToCompile.Name, ".sv") + ".v"
	vFilePath := filepath.Join(baseWorkerDir, vFileName)

	// Check if the .v file exists (sv2v transformation should have created it)
	if _, err := os.Stat(vFilePath); err == nil {
		sch.debug.Debug(
			"[%s] Found .v file at %s, creating sv2v simulator variants",
			workerID,
			vFilePath,
		)

		// Parse the .v file to create a VerilogFile object
		vFileContent, err := os.ReadFile(vFilePath)
		if err != nil {
			sch.debug.Warn("[%s] Failed to read .v file %s: %v", workerID, vFilePath, err)
		} else {
			vFile, err := verilog.ParseVerilog(string(vFileContent), sch.verbose)
			if err != nil {
				sch.debug.Warn("[%s] Failed to parse .v file %s: %v", workerID, vFilePath, err)
			} else {
				vFile.Name = vFileName

				// 1. Icarus Verilog sv2v variant
				ivWorkDir2 := filepath.Join(baseWorkerDir, "icarus_sv2v") // Use different directory
				if err := os.MkdirAll(ivWorkDir2, 0o755); err != nil {
					sch.debug.Warn(
						"[%s] Failed to create IVerilog sv2v directory %s: %v",
						workerID,
						ivWorkDir2,
						err,
					)
					setupErrors = append(setupErrors, fmt.Sprintf("iverilog_sv2v_mkdir: %v", err))
				} else {
					// Copy .v file to sv2v directory
					ivVFilePath := filepath.Join(ivWorkDir2, vFileName)
					if err := utils.CopyFile(vFilePath, ivVFilePath); err != nil {
						sch.debug.Warn(
							"[%s] Failed to copy .v file to IVerilog sv2v directory: %v",
							workerID,
							err,
						)
					} else {
						ivsim2 := simulator.NewIVerilogSimulator(ivWorkDir2, sch.verbose)
						sch.debug.Debug("[%s] Compiling IVerilog sv2v simulator in %s", workerID, ivWorkDir2)

						compileCtx2, compileCancel2 := context.WithTimeout(ctx, sch.timeouts.CompilationTimeout)
						defer compileCancel2()

						if err := ivsim2.Compile(compileCtx2); err != nil {
							sch.debug.Warn("[%s] Failed to compile IVerilog sv2v: %v", workerID, err)
							setupErrors = append(setupErrors, fmt.Sprintf("iverilog_sv2v: %v", err))
						} else {
							sch.debug.Debug("[%s] IVerilog sv2v compiled successfully.", workerID)
							compiledSims = append(compiledSims, &SimInstance{
								Name:      "icaru2",
								Simulator: ivsim2,
								Prefix:    "iv2_",
							})
						}
					}
				}

				// 2. Verilator O0 sv2v variant
				vlO0WorkDir2 := filepath.Join(baseWorkerDir, "vl_O0_sv2v")
				if err := os.MkdirAll(vlO0WorkDir2, 0o755); err != nil {
					sch.debug.Warn(
						"[%s] Failed to create Verilator O0 sv2v directory %s: %v",
						workerID,
						vlO0WorkDir2,
						err,
					)
					setupErrors = append(setupErrors, fmt.Sprintf("verilator_O0_sv2v_mkdir: %v", err))
				} else {
					vlsim0_2 := simulator.NewVerilatorSimulator(
						vlO0WorkDir2,
						vFile,
						workerModuleName,
						false,
						sch.verbose,
					)
					sch.debug.Debug("[%s] Compiling Verilator O0 sv2v simulator in %s", workerID, vlO0WorkDir2)

					compileCtx0_2, compileCancel0_2 := context.WithTimeout(ctx, sch.timeouts.CompilationTimeout)
					defer compileCancel0_2()

					if err := vlsim0_2.Compile(compileCtx0_2); err != nil {
						sch.debug.Warn("[%s] Failed to compile Verilator O0 sv2v: %v", workerID, err)
						setupErrors = append(setupErrors, fmt.Sprintf("verilator_O0_sv2v: %v", err))
					} else {
						sch.debug.Debug("[%s] Verilator O0 sv2v compiled successfully.", workerID)
						compiledSims = append(compiledSims, &SimInstance{
							Name:      "vtor20",
							Simulator: vlsim0_2,
							Prefix:    "vl20_",
						})
					}
				}

				// 3. Verilator O3 sv2v variant
				vlO3WorkDir2 := filepath.Join(baseWorkerDir, "vl_O3_sv2v")
				if err := os.MkdirAll(vlO3WorkDir2, 0o755); err != nil {
					sch.debug.Warn(
						"[%s] Failed to create Verilator O3 sv2v directory %s: %v",
						workerID,
						vlO3WorkDir2,
						err,
					)
					setupErrors = append(setupErrors, fmt.Sprintf("verilator_O3_sv2v_mkdir: %v", err))
				} else {
					vlsim3_2 := simulator.NewVerilatorSimulator(
						vlO3WorkDir2,
						vFile,
						workerModuleName,
						true,
						sch.verbose,
					)
					sch.debug.Debug("[%s] Compiling Verilator O3 sv2v simulator in %s", workerID, vlO3WorkDir2)

					compileCtx3_2, compileCancel3_2 := context.WithTimeout(ctx, sch.timeouts.CompilationTimeout)
					defer compileCancel3_2()

					if err := vlsim3_2.Compile(compileCtx3_2); err != nil {
						sch.debug.Warn("[%s] Failed to compile Verilator O3 sv2v: %v", workerID, err)
						setupErrors = append(setupErrors, fmt.Sprintf("verilator_O3_sv2v: %v", err))
					} else {
						sch.debug.Debug("[%s] Verilator O3 sv2v compiled successfully.", workerID)
						compiledSims = append(compiledSims, &SimInstance{
							Name:      "vtor23",
							Simulator: vlsim3_2,
							Prefix:    "vl23_",
						})
					}
				}

				// 4. CXXRTL sv2v variant
				cxxrtlWorkDir2 := filepath.Join(baseWorkerDir, "cxxrtl_sim_sv2v")
				if err := os.MkdirAll(cxxrtlWorkDir2, 0o755); err != nil {
					sch.debug.Warn(
						"[%s] Failed to create CXXRTL sv2v directory %s: %v",
						workerID,
						cxxrtlWorkDir2,
						err,
					)
					setupErrors = append(setupErrors, fmt.Sprintf("CXXRTL_sv2v_mkdir: %v", err))
				} else {
					// Determine includeDir (same logic as original CXXRTL)
					yosysCmd := exec.Command("yosys-config", "--datdir")
					var yosysOut bytes.Buffer
					var yosysErr bytes.Buffer
					yosysCmd.Stdout = &yosysOut
					yosysCmd.Stderr = &yosysErr

					var includeDir string
					if err := yosysCmd.Run(); err == nil {
						yosysDatDir := strings.TrimSpace(yosysOut.String())
						potentialPath := filepath.Join(
							yosysDatDir,
							"include",
							"backends",
							"cxxrtl",
							"runtime",
						)
						if _, statErr := os.Stat(potentialPath); statErr == nil {
							includeDir = potentialPath
						}
					}

					cxsim2 := simulator.NewCXXRTLSimulator(
						cxxrtlWorkDir2,
						vFile.Name,
						workerModuleName,
						includeDir,
						false, // optimized
						false, // useSlang
						sch.verbose,
					)
					sch.debug.Debug("[%s] Compiling CXXRTL sv2v simulator in %s", workerID, cxxrtlWorkDir2)

					compileCtxCXX2, compileCancelCXX2 := context.WithTimeout(ctx, sch.timeouts.CompilationTimeout)
					defer compileCancelCXX2()

					if err := cxsim2.Compile(compileCtxCXX2); err != nil {
						sch.debug.Warn(
							"[%s] CXXRTL sv2v compilation failed in %s: %v",
							workerID,
							cxxrtlWorkDir2,
							err,
						)
						setupErrors = append(setupErrors, fmt.Sprintf("CXXRTL_sv2v compile error: %v", err))
					} else {
						sch.debug.Debug(
							"[%s] Successfully compiled CXXRTL sv2v simulator in %s.",
							workerID,
							cxxrtlWorkDir2,
						)
						compiledSims = append(compiledSims, &SimInstance{
							Name:      "CXXRT2",
							Simulator: cxsim2,
							Prefix:    "cxx2_vanilla_",
						})
					}
				}

				// 5. CXXRTL with Slang sv2v variant
				cxxrtlSlangWorkDir2 := filepath.Join(baseWorkerDir, "cxxrtl_slang_sim_sv2v")
				if err := os.MkdirAll(cxxrtlSlangWorkDir2, 0o755); err != nil {
					sch.debug.Warn(
						"[%s] Failed to create CXXRTL Slang sv2v directory %s: %v",
						workerID,
						cxxrtlSlangWorkDir2,
						err,
					)
					setupErrors = append(setupErrors, fmt.Sprintf("CXXRTL_slang_sv2v_mkdir: %v", err))
				} else {
					// Use same includeDir determination logic
					yosysCmd := exec.Command("yosys-config", "--datdir")
					var yosysOut bytes.Buffer
					var yosysErr bytes.Buffer
					yosysCmd.Stdout = &yosysOut
					yosysCmd.Stderr = &yosysErr

					var includeDir string
					if err := yosysCmd.Run(); err == nil {
						yosysDatDir := strings.TrimSpace(yosysOut.String())
						potentialPath := filepath.Join(
							yosysDatDir,
							"include",
							"backends",
							"cxxrtl",
							"runtime",
						)
						if _, statErr := os.Stat(potentialPath); statErr == nil {
							includeDir = potentialPath
						}
					}

					cxSlangSim2 := simulator.NewCXXRTLSimulator(
						cxxrtlSlangWorkDir2,
						vFile.Name,
						workerModuleName,
						includeDir,
						false, // optimized
						true,  // useSlang
						sch.verbose,
					)
					sch.debug.Debug(
						"[%s] Compiling CXXRTL Slang sv2v simulator in %s",
						workerID,
						cxxrtlSlangWorkDir2,
					)

					compileCtxSlang2, compileCancelSlang2 := context.WithTimeout(ctx, sch.timeouts.CompilationTimeout)
					defer compileCancelSlang2()

					if err := cxSlangSim2.Compile(compileCtxSlang2); err != nil {
						sch.debug.Warn(
							"[%s] CXXRTL Slang sv2v compilation failed in %s: %v",
							workerID,
							cxxrtlSlangWorkDir2,
							err,
						)
						setupErrors = append(setupErrors, fmt.Sprintf("CXXRTL_slang_sv2v compile error: %v", err))
					} else {
						sch.debug.Debug(
							"[%s] Successfully compiled CXXRTL Slang sv2v simulator in %s.",
							workerID,
							cxxrtlSlangWorkDir2,
						)
						compiledSims = append(compiledSims, &SimInstance{
							Name:      "CXXSL2",
							Simulator: cxSlangSim2,
							Prefix:    "cxx2_slang_",
						})
					}
				}
			}
		}
	} else {
		sch.debug.Debug(
			"[%s] No .v file found at %s, skipping sv2v simulator variants",
			workerID,
			vFilePath,
		)
	}

	if len(compiledSims) == 0 {
		return nil, fmt.Errorf(
			"[%s] no simulators compiled successfully. Errors: %s",
			workerID,
			strings.Join(setupErrors, "; "),
		)
	}

	sch.debug.Info("[%s] Successfully compiled %d simulators.", workerID, len(compiledSims))
	return compiledSims, nil
}

func (sch *Scheduler) worker(
	ctx context.Context,
	testCases <-chan int,
	moduleToTest *verilog.Module,
	workerNum int,
) error {
	var lastSetupError error
	workerID := fmt.Sprintf("worker_%d_%d", workerNum, time.Now().UnixNano())
	var strategy Strategy
	switch sch.strategyName {
	case "random":
		strategy = &RandomStrategy{}
	case "smart":
		strategy = &SmartStrategy{}
	default:
		return fmt.Errorf("Unknown strategy: %s", sch.strategyName)
	}

	strategy.SetModule(moduleToTest)

	for attempt := 0; attempt < sch.maxAttempts; attempt++ {
		workerCompleteID := fmt.Sprintf(
			"%s_%d",
			workerID,
			attempt,
		)
		sch.debug.Debug(
			"[%s] Starting worker attempt %d/%d",
			workerCompleteID,
			attempt+1,
			sch.maxAttempts,
		)

		setupOk, err := sch.performWorkerAttempt(
			ctx,
			workerCompleteID,
			testCases,
			moduleToTest,
			strategy,
		)

		if setupOk {
			sch.debug.Info("[%s] Worker completed its tasks.", workerID)
			return nil
		}

		// Setup failed for this attempt
		lastSetupError = err
		sch.debug.Warn(
			"[%s] Worker attempt %d/%d failed setup for module %s from file %s",
			workerCompleteID,
			attempt+1,
			sch.maxAttempts,
			moduleToTest.Name,
			sch.svFile.Name,
		)

		if attempt < sch.maxAttempts-1 {
			sch.debug.Info(
				"[%s] Retrying worker initialization after a short delay...",
				workerCompleteID,
			)
			time.Sleep(time.Duration(attempt+1) * time.Second) // Optional backoff
		}
	}

	return fmt.Errorf(
		"[%s] Worker failed to initialize after %d attempts: %v",
		workerID,
		sch.maxAttempts,
		lastSetupError,
	)
}
