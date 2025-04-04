package utils

import (
	"fmt"
	"os"
	"path/filepath"
	"sync"
)

// TMP_DIR is the directory where all generated files are stored
const TMP_DIR = "tmp_gen"
const MISMATCHES_DIR = "mismatches"

// Global mutex for file operations
var fileOpMutex sync.Mutex

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

	return os.WriteFile(filename, []byte{data + '0'}, 0644)
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

// Thread-safe version of WriteFileContent
func WriteFileContent(filename string, content string) error {
	fileOpMutex.Lock()
	defer fileOpMutex.Unlock()

	return os.WriteFile(filename, []byte(content), 0644)
}

// TmpPath returns the path within the temporary directory
func TmpPath(filename string) string {
	return filepath.Join(TMP_DIR, filename)
}

// Thread-safe version of CopyFile
func CopyFile(src, dst string) error {
	fileOpMutex.Lock()
	defer fileOpMutex.Unlock()

	data, err := os.ReadFile(src)
	if err != nil {
		return err
	}
	return os.WriteFile(dst, data, 0644)
}

// Thread-safe version of FileExists
func FileExists(path string) bool {
	fileOpMutex.Lock()
	defer fileOpMutex.Unlock()

	info, err := os.Stat(path)
	if err != nil {
		return false
	}
	return !info.IsDir() && info.Size() > 0
}
