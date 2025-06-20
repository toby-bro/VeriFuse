package utils

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"sync"
)

// Common directory paths
var (
	TMP_DIR        = "dist"
	MISMATCHES_DIR = "mismatches"
	DEBUG_LOGS_DIR = "debug_logs"
	DEBUG          = false
)

// Global mutex for file operations
var fileOpMutex sync.Mutex

// EnsureDirs creates required directories if they don't exist
func EnsureDirs() error {
	dirs := []string{
		TMP_DIR,
		MISMATCHES_DIR,
		DEBUG_LOGS_DIR,
	}

	for _, dir := range dirs {
		if err := os.MkdirAll(dir, 0o755); err != nil {
			return fmt.Errorf("failed to create directory %s: %v", dir, err)
		}
	}

	return nil
}

func EnsureDirWithPath(path string) error {
	if DEBUG {
		fmt.Printf("%s[-] Creating directory %s%s\n", ColorBlue, path, ColorReset)
	}
	if err := os.MkdirAll(path, 0o755); err != nil {
		return fmt.Errorf("failed to create directory %s: %v", path, err)
	}
	return nil
}

// EnsureTmpDir creates the temporary directory if it doesn't exist
func EnsureTmpDir() error {
	if _, err := os.Stat(TMP_DIR); os.IsNotExist(err) {
		return os.MkdirAll(TMP_DIR, 0o755)
	}
	return nil
}

func EnsureFileWritten(filename string, err error, expectedSize int) error {
	if err != nil {
		return fmt.Errorf("failed to write file %s: %v", filename, err)
	}
	info, err := os.Stat(filename)
	if err != nil {
		return fmt.Errorf("failed to stat file %s: %v", filename, err)
	}
	if expectedSize != 0 && info.Size() != int64(expectedSize) {
		return fmt.Errorf("file size mismatch: expected %d, got %d", expectedSize, info.Size())
	}
	return nil
}

// Thread-safe version of WriteHexFile
func WriteHexFile(filename string, data uint32) error {
	fileOpMutex.Lock()
	defer fileOpMutex.Unlock()

	hexData := fmt.Sprintf("%08x\n", data)
	err := os.WriteFile(filename, []byte(hexData), 0o644)

	return EnsureFileWritten(filename, err, len(hexData))
}

// Thread-safe version of WriteBinFile
func WriteBinFile(filename string, data uint8) error {
	fileOpMutex.Lock()
	defer fileOpMutex.Unlock()

	err := os.WriteFile(filename, []byte{data + '0'}, 0o644)
	return EnsureFileWritten(filename, err, 1)
}

// Thread-safe version of ReadFileContent
func ReadFileContent(filename string) (string, error) {
	fileOpMutex.Lock()
	defer fileOpMutex.Unlock()

	content, err := os.ReadFile(filename)
	if err != nil {
		return "", fmt.Errorf("failed to read file %s: %v", filename, err)
	}
	return string(content), nil
}

// WriteFileContent writes content to a file, creating directories as needed
func WriteFileContent(path string, content string) error {
	fileOpMutex.Lock()
	defer fileOpMutex.Unlock()

	if DEBUG {
		fmt.Printf("%s[-] Writing file %s%s\n", ColorBlue, path, ColorReset)
	}
	// Ensure the directory exists
	dir := filepath.Dir(path)
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return fmt.Errorf("failed to create directory %s: %v", dir, err)
	}

	err := os.WriteFile(path, []byte(content), 0o644)
	return EnsureFileWritten(path, err, len(content))
}

// CopyFile copies a file from src to dst
func CopyFile(src, dst string) error {
	fileOpMutex.Lock()
	defer fileOpMutex.Unlock()

	if DEBUG {
		fmt.Printf("%s[-] Copying file %s to %s%s\n", ColorBlue, src, dst, ColorReset)
	}
	// Ensure the destination directory exists
	dir := filepath.Dir(dst)
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return fmt.Errorf("failed to create directory %s: %v", dir, err)
	}

	// Read source file
	data, err := os.ReadFile(src)
	if err != nil {
		return fmt.Errorf("failed to read source file: %v", err)
	}

	// Write destination file
	err = os.WriteFile(dst, data, 0o644)
	return EnsureFileWritten(dst, err, len(data))
}

// FileExists checks if a file exists and is not a directory
func FileExists(path string) bool {
	fileOpMutex.Lock()
	defer fileOpMutex.Unlock()

	info, err := os.Stat(path)
	if os.IsNotExist(err) {
		return false
	}
	return !info.IsDir()
}

func GetRootDir() (string, error) {
	cwd, err := os.Getwd()
	if err != nil {
		return "", fmt.Errorf("failed to get current working directory: %w", err)
	}
	dir := cwd
	for {
		// Check if .git exists in the current directory
		gitPath := filepath.Join(dir, ".git")
		stat, err := os.Stat(gitPath)
		if err == nil && stat.IsDir() {
			return dir, nil // Found the repository root
		}
		// Handle errors other than "not found"
		if err != nil && !os.IsNotExist(err) {
			return "", fmt.Errorf("error checking for .git directory at %s: %w", gitPath, err)
		}

		// Move to the parent directory
		parentDir := filepath.Dir(dir)
		if parentDir == dir {
			// Reached the filesystem root without finding .git
			return "", fmt.Errorf(
				"failed to find repository root (.git directory) starting from %s",
				cwd,
			)
		}
		dir = parentDir
	}
}

// ChangeExtension changes the file extension of the given path to newExt
// DO NOT PUT A DOT IN newExt
func ChangeExtension(path, newExt string) string {
	ext := filepath.Ext(path)
	base := strings.TrimSuffix(path, ext)
	newPath := fmt.Sprintf("%s.%s", base, newExt)
	return newPath
}

// AddSuffixToPath adds a suffix before the file extension in the given path
func AddSuffixToPath(path, suffix string) string {
	ext := filepath.Ext(path)
	base := strings.TrimSuffix(path, ext)
	newPath := fmt.Sprintf("%s%s%s", base, suffix, ext)
	return newPath
}
