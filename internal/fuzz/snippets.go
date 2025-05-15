package fuzz

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"

	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

type Snippet struct {
	Name       string
	Module     *verilog.Module
	ParentFile *verilog.VerilogFile
}

var (
	snippets     = []*Snippet{}
	verilogFiles = []*verilog.VerilogFile{}
)

func findSnippetFiles() ([]string, error) {
	repoRoot, err := utils.GetRootDir()
	if err != nil || repoRoot == "" {
		return nil, fmt.Errorf("failed to find repository root: %w", err)
	}

	snippetsDir := filepath.Join(repoRoot, "snippets")

	if _, err := os.Stat(snippetsDir); os.IsNotExist(err) {
		return nil, fmt.Errorf("snippets directory '%s' does not exist", snippetsDir)
	} else if err != nil {
		return nil, fmt.Errorf("failed to access snippets directory '%s': %w", snippetsDir, err)
	}

	sourceFiles, err := filepath.Glob(filepath.Join(snippetsDir, "*.sv"))
	logger.Debug("Loading snippets from directory: %s", snippetsDir)
	if err != nil {
		return nil, err
	}
	return sourceFiles, nil
}

func loadSnippets() error {
	sourceFiles, err := findSnippetFiles()
	if err != nil {
		return fmt.Errorf("failed to find snippet files: %v", err)
	}
	for _, snippetFile := range sourceFiles {
		fileContent, err := utils.ReadFileContent(snippetFile)
		if err != nil {
			return fmt.Errorf("failed to read snippet file %s: %v", snippetFile, err)
		}
		verilogFile, err := verilog.ParseVerilog(fileContent, verbose)
		verilogFile.Name = snippetFile
		if err != nil || verilogFile == nil {
			return err
		}
		for _, module := range verilogFile.Modules {
			if module.Name == "" {
				return fmt.Errorf("module name is empty in file %s", snippetFile)
			}
			snippets = append(snippets, &Snippet{
				Name:       module.Name,
				Module:     module,
				ParentFile: verilogFile,
			})
			verilogFiles = append(verilogFiles, verilogFile)
		}
	}
	logger.Debug("Loaded %d snippets from %d files", len(snippets), len(sourceFiles))
	return nil
}

func getSnippets() ([]*Snippet, []*verilog.VerilogFile, error) {
	if len(snippets) == 0 {
		err := loadSnippets()
		if err != nil {
			return nil, nil, fmt.Errorf("failed to load snippets: %v", err)
		}
	}
	return snippets, verilogFiles, nil
}

func getRandomSnippet() (*Snippet, error) {
	snippets, _, err := getSnippets()
	if err != nil {
		return nil, fmt.Errorf("failed to get snippets: %v", err)
	}
	if len(snippets) == 0 {
		return nil, errors.New("no snippets available")
	}
	randomIndex := utils.RandomInt(0, len(snippets)-1)
	return snippets[randomIndex], nil
}
