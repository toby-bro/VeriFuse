package utils

import (
	"io"
	"os"
	"path/filepath"
	"strings"
)

// CopyDir recursively copies a directory
func CopyDir(src string, dst string) error {
	// Get properties of source directory
	srcInfo, err := os.Stat(src)
	if err != nil {
		return err
	}

	// Create destination directory
	if err = os.MkdirAll(dst, srcInfo.Mode()); err != nil {
		return err
	}

	// Read source directory
	entries, err := os.ReadDir(src)
	if err != nil {
		return err
	}

	// Copy each entry
	for _, entry := range entries {
		srcPath := filepath.Join(src, entry.Name())
		dstPath := filepath.Join(dst, entry.Name())

		if entry.IsDir() {
			// Recursive copy for directories
			if err = CopyDir(srcPath, dstPath); err != nil {
				return err
			}
		} else {
			// Copy files
			if err = CopyFile(srcPath, dstPath); err != nil {
				return err
			}
		}
	}
	return nil
}

// EnhancedCopyFile copies a file with progress tracking for large files
func EnhancedCopyFile(src, dst string) error {
	sourceFile, err := os.Open(src)
	if err != nil {
		return err
	}
	defer sourceFile.Close()

	// Get file info
	_, err = sourceFile.Stat()
	if err != nil {
		return err
	}

	// Create destination file
	destFile, err := os.Create(dst)
	if err != nil {
		return err
	}
	defer destFile.Close()

	// Copy with buffer
	buf := make([]byte, 1024*1024) // 1MB buffer
	for {
		n, err := sourceFile.Read(buf)
		if err != nil && err != io.EOF {
			return err
		}
		if n == 0 {
			break
		}

		if _, err := destFile.Write(buf[:n]); err != nil {
			return err
		}
	}
	return nil
}

// TrimEmptyLines removes leading and trailing empty lines from a string
func TrimEmptyLines(input string) string {
	lines := strings.Split(input, "\n")
	if lines[0] == "" {
		lines = lines[1:] // Remove leading empty line
	}
	if lines[len(lines)-1] == "" {
		lines = lines[:len(lines)-1] // Remove trailing empty line
	}
	return strings.Join(lines, "\n")
}
