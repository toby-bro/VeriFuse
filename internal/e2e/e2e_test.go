package e2e

import (
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
)

// findProjectRoot searches upwards from the current file to find the directory containing go.mod
func findProjectRoot() (string, error) {
	_, b, _, ok := runtime.Caller(0)
	if !ok {
		return "", errors.New("cannot get caller information")
	}
	basepath := filepath.Dir(b)
	// Navigate up from internal/e2e to the root
	for i := 0; i < 3; i++ { // Adjust depth if package structure changes
		goModPath := filepath.Join(basepath, "go.mod")
		if _, err := os.Stat(goModPath); err == nil {
			return basepath, nil
		}
		parent := filepath.Dir(basepath)
		if parent == basepath {
			break // Avoid infinite loop if already at root
		}
		basepath = parent
	}
	return "", errors.New("go.mod not found within 3 levels up from test file")
}

// buildPfuzz ensures the pfuzz binary exists in the project root, building it if necessary.
func buildPfuzz(projectRoot string) (string, error) {
	pfuzzPath := filepath.Join(projectRoot, "pfuzz")
	cmdPath := filepath.Join(projectRoot, "cmd", "pfuzz", "main.go")

	// Check if binary exists
	if _, err := os.Stat(pfuzzPath); err == nil {
		// TODO: Optionally check if binary is up-to-date with source? For now, assume existing is fine.
		// fmt.Println("Using existing pfuzz binary.")
		return pfuzzPath, nil
	}

	fmt.Println("Building pfuzz binary...")
	cmd := exec.Command("go", "build", "-o", pfuzzPath, cmdPath)
	cmd.Dir = projectRoot // Run 'go build' from the project root
	output, err := cmd.CombinedOutput()
	if err != nil {
		return "", fmt.Errorf("failed to build pfuzz binary: %v\nOutput:\n%s", err, string(output))
	}
	fmt.Println("Build successful.")
	return pfuzzPath, nil
}

// copyFile copies a file from src to dst.
func copyFile(src, dst string) error {
	sourceFileStat, err := os.Stat(src)
	if err != nil {
		return err
	}

	if !sourceFileStat.Mode().IsRegular() {
		return fmt.Errorf("%s is not a regular file", src)
	}

	source, err := os.Open(src)
	if err != nil {
		return err
	}
	defer source.Close()

	// Ensure destination directory exists
	dstDir := filepath.Dir(dst)
	if err := os.MkdirAll(dstDir, 0o755); err != nil {
		return err
	}

	destination, err := os.Create(dst)
	if err != nil {
		return err
	}
	defer destination.Close()

	_, err = io.Copy(destination, source)
	if err != nil {
		return err
	}

	// Copy permissions
	err = os.Chmod(dst, sourceFileStat.Mode())
	return err
}

// TestPfuzzEndToEnd runs the pfuzz command on various test files.
func TestPfuzzEndToEnd(t *testing.T) {
	projectRoot, err := findProjectRoot()
	if err != nil {
		t.Fatalf("Failed to find project root: %v", err)
	}

	pfuzzBinaryAbs, err := buildPfuzz(projectRoot)
	if err != nil {
		t.Fatalf("Failed to ensure pfuzz binary exists: %v", err)
	}
	pfuzzBinaryName := filepath.Base(pfuzzBinaryAbs) // Just the binary name, e.g., "pfuzz"

	// Define test files directory relative to project root
	testFilesDir := filepath.Join(projectRoot, "testfiles", "sv")

	// Find test files
	var testFiles []string
	err = filepath.Walk(testFilesDir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		// Skip directories and files in specific subdirectories
		if !info.IsDir() && strings.HasSuffix(path, ".sv") &&
			!strings.Contains(path, "/unsupported/") &&
			!strings.Contains(path, "/fail/") &&
			!strings.Contains(path, "/mock/") {
			relPath, _ := filepath.Rel(projectRoot, path) // Get path relative to root for clarity
			testFiles = append(testFiles, relPath)
		}
		return nil
	})
	if err != nil {
		t.Fatalf("Failed to walk testfiles directory: %v", err)
	}

	if len(testFiles) == 0 {
		t.Fatal("No test files found.")
	}

	t.Logf("Found %d test files.", len(testFiles))

	// Clean shared directories once before starting parallel tests (optional, good practice)
	_ = os.RemoveAll(filepath.Join(projectRoot, "dist"))
	_ = os.RemoveAll(filepath.Join(projectRoot, "mismatches"))
	_ = os.RemoveAll(filepath.Join(projectRoot, "debug_logs"))

	// Run test for each file
	for _, testFileRelPath := range testFiles {
		// Capture loop variable for use in the closure by shadowing
		testFileAbsPath := filepath.Join(projectRoot, testFileRelPath)
		testFileName := filepath.Base(testFileAbsPath)
		// Sanitize test name for directory creation if needed (replace non-alphanumeric)
		safeTestName := strings.ReplaceAll(strings.TrimSuffix(testFileName, ".sv"), ".", "_")

		t.Run(testFileName, func(t *testing.T) {
			t.Parallel() // Run tests in parallel

			// Create a unique temporary directory for this test run
			tempTestDir, err := os.MkdirTemp("", "pfuzz_e2e_"+safeTestName+"_*")
			if err != nil {
				t.Fatalf("Failed to create temp dir for test %s: %v", testFileName, err)
			}
			// Ensure cleanup happens even on test failure/panic
			t.Cleanup(func() { os.RemoveAll(tempTestDir) })

			// Copy pfuzz binary to the temp directory
			localPfuzzPath := filepath.Join(tempTestDir, pfuzzBinaryName)
			if err := copyFile(pfuzzBinaryAbs, localPfuzzPath); err != nil {
				t.Fatalf("Failed to copy pfuzz binary for test %s: %v", testFileName, err)
			}

			// Copy the test file to the temp directory
			localTestFilePath := filepath.Join(tempTestDir, testFileName)
			if err := copyFile(testFileAbsPath, localTestFilePath); err != nil {
				t.Fatalf("Failed to copy test file %s: %v", testFileName, err)
			}

			// Construct command - run pfuzz from within the temp directory
			// Use the local test file name relative to the temp dir
			args := []string{
				"-n", "10", // Keep test runs short
				"-strategy", "random",
				"-workers", "1", // Keep workers=1 for simplicity within each parallel test
				"-file", testFileName, // Use the relative path within tempTestDir
			}

			// Use the local pfuzz binary path
			cmd := exec.Command("./"+pfuzzBinaryName, args...)
			cmd.Dir = tempTestDir // Run the command from the isolated temp directory

			// Execute command and capture output
			output, err := cmd.CombinedOutput()

			// Check exit code
			if err != nil {
				// Include logs from the test-specific directories if they exist
				mismatchDir := filepath.Join(tempTestDir, "mismatches")
				debugDir := filepath.Join(tempTestDir, "debug_logs")
				var extraInfo strings.Builder
				extraInfo.WriteString("\n--- Extra Info ---\n")

				// Helper function to read files in a directory
				readDirContents := func(dirPath string, prefix string) {
					if _, err := os.Stat(dirPath); !os.IsNotExist(err) {
						extraInfo.WriteString(fmt.Sprintf("Contents of %s:\n", dirPath))
						err := filepath.WalkDir(
							dirPath,
							func(path string, d os.DirEntry, err error) error {
								if err != nil {
									extraInfo.WriteString(
										fmt.Sprintf("  Error accessing path %s: %v\n", path, err),
									)
									return err // Propagate error if needed, or skip
								}
								if !d.IsDir() {
									content, readErr := os.ReadFile(path)
									relPath, _ := filepath.Rel(dirPath, path)
									if readErr != nil {
										extraInfo.WriteString(
											fmt.Sprintf(
												"  %s%s: Error reading file: %v\n",
												prefix,
												relPath,
												readErr,
											),
										)
									} else {
										extraInfo.WriteString(fmt.Sprintf("  %s%s:\n%s\n", prefix, relPath, string(content)))
									}
								}
								return nil
							},
						)
						if err != nil {
							extraInfo.WriteString(
								fmt.Sprintf("  Error walking directory %s: %v\n", dirPath, err),
							)
						}
					} else {
						extraInfo.WriteString(dirPath + " directory not found.\n")
					}
				}

				// Read contents of mismatch and debug directories
				readDirContents(mismatchDir, "mismatches/")
				readDirContents(debugDir, "debug_logs/")
				extraInfo.WriteString("--- End Extra Info ---\n")

				t.Errorf(
					"pfuzz command failed for %s in %s with error: %v\nArgs: %v\nOutput:\n%s%s",
					testFileRelPath,
					tempTestDir,
					err,
					args,
					string(output),
					extraInfo.String(),
				)

				t.Errorf("pfuzz command failed for %s in %s with error: %v\nArgs: %v\nOutput:\n%s",
					testFileRelPath, tempTestDir, err, args, string(output))
			} else {
				// Optional: Check output for specific success messages if needed
				t.Logf("pfuzz command succeeded for %s in %s", testFileRelPath, tempTestDir)
			}
		})
	}
}
