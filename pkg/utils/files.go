package utils

import (
	"fmt"
	"os"
	"path/filepath"
)

// TMP_DIR is the directory where all generated files are stored
const TMP_DIR = "tmp_gen"
const MISMATCHES_DIR = "mismatches"

// EnsureDirs creates necessary directories if they don't exist
func EnsureDirs() error {
	if err := os.MkdirAll(TMP_DIR, 0755); err != nil {
		return fmt.Errorf("failed to create tmp directory: %v", err)
	}
	if err := os.MkdirAll(MISMATCHES_DIR, 0755); err != nil {
		return fmt.Errorf("failed to create mismatches directory: %v", err)
	}
	return nil
}

// EnsureTmpDir creates the temporary directory if it doesn't exist
func EnsureTmpDir() error {
	if _, err := os.Stat(TMP_DIR); os.IsNotExist(err) {
		return os.MkdirAll(TMP_DIR, 0755)
	}
	return nil
}

// WriteHexFile writes a uint32 value as hex to a file
func WriteHexFile(filename string, data uint32) error {
	f, err := os.Create(filename)
	if err != nil {
		return err
	}
	defer f.Close()
	fmt.Fprintf(f, "%08x\n", data)
	return nil
}

// WriteBinFile writes a uint8 value as binary to a file
func WriteBinFile(filename string, data uint8) error {
	return os.WriteFile(filename, []byte{data + '0'}, 0644)
}

// ReadFileContent reads the content of a file as a string
func ReadFileContent(filename string) (string, error) {
	content, err := os.ReadFile(filename)
	if err != nil {
		return "", fmt.Errorf("failed to read file %s: %v", filename, err)
	}
	return string(content), nil
}

// WriteFileContent writes content to a file
func WriteFileContent(filename string, content string) error {
	return os.WriteFile(filename, []byte(content), 0644)
}

// TmpPath returns the path within the temporary directory
func TmpPath(filename string) string {
	return filepath.Join(TMP_DIR, filename)
}
