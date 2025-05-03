package utils

import (
	"fmt"
	"os"
	"path/filepath"
	"sync"
)

// Common directory paths
var (
	TMP_DIR        = "tmp_gen"
	MISMATCHES_DIR = "mismatches"
	DEBUG_LOGS_DIR = "debug_logs"
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

// EnsureTmpDir creates the temporary directory if it doesn't exist
func EnsureTmpDir() error {
	if _, err := os.Stat(TMP_DIR); os.IsNotExist(err) {
		return os.MkdirAll(TMP_DIR, 0o755)
	}
	return nil
}

// Thread-safe version of WriteHexFile
func WriteHexFile(filename string, data uint32) error {
	fileOpMutex.Lock()
	defer fileOpMutex.Unlock()

	f, err := os.Create(filename)
	if err != nil {
		return err
	}
	defer f.Close()
	fmt.Fprintf(f, "%08x\n", data)
	return nil
}

// Thread-safe version of WriteBinFile
func WriteBinFile(filename string, data uint8) error {
	fileOpMutex.Lock()
	defer fileOpMutex.Unlock()

	return os.WriteFile(filename, []byte{data + '0'}, 0o644)
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

	// Ensure the directory exists
	dir := filepath.Dir(path)
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return fmt.Errorf("failed to create directory %s: %v", dir, err)
	}

	return os.WriteFile(path, []byte(content), 0o644)
}

// TmpPath returns the path within the temporary directory
func TmpPath(filename string) string {
	return filepath.Join(TMP_DIR, filename)
}

// CopyFile copies a file from src to dst
func CopyFile(src, dst string) error {
	fileOpMutex.Lock()
	defer fileOpMutex.Unlock()

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
	return os.WriteFile(dst, data, 0o644)
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

// TrimWhitespace removes whitespace, newlines, and tabs from a string
func TrimWhitespace(s string) string {
	// Custom implementation to handle whitespace
	result := ""
	for _, c := range s {
		if c != ' ' && c != '\n' && c != '\r' && c != '\t' {
			result += string(c)
		}
	}
	return result
}
