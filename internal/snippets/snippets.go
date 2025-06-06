package snippets

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
	logger       = *utils.NewDebugLogger(1)
)

func findSnippetFiles() ([]string, error) {
	repoRoot, err := utils.GetRootDir()
	if err != nil || repoRoot == "" {
		return nil, fmt.Errorf("failed to find repository root: %w", err)
	}

	snippetsDir := filepath.Join(repoRoot, "isolated")

	if _, err := os.Stat(snippetsDir); os.IsNotExist(err) {
		return nil, fmt.Errorf("snippets directory '%s' does not exist", snippetsDir)
	} else if err != nil {
		return nil, fmt.Errorf("failed to access snippets directory '%s': %w", snippetsDir, err)
	}

	sourceFiles, err := filepath.Glob(filepath.Join(snippetsDir, "**/*.sv"))
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
		verilogFile, err := verilog.ParseVerilog(fileContent, logger.GetVerboseLevel())
		verilogFile.Name = snippetFile
		if err != nil || verilogFile == nil {
			return err
		}
		for _, module := range verilogFile.Modules {
			if module.Name == "" {
				return fmt.Errorf("module name is empty in file %s", snippetFile)
			}
			if module.Name == "top" {
				module.Name = "topi"
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

func GetRandomSnippet(verbose int) (*Snippet, error) {
	logger.SetVerboseLevel(verbose)
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

func dfsDependencies(
	nodeName string,
	parentVF *verilog.VerilogFile,
	targetFile *verilog.VerilogFile,
) {
	parentNode, ok := parentVF.DependencyMap[nodeName]
	if !ok {
		return
	}

	for _, dep := range parentNode.DependsOn {
		if _, found := targetFile.DependencyMap[dep]; found {
			continue
		}
		targetFile.DependencyMap[dep] = parentVF.DependencyMap[dep]
		if s, found := parentVF.Structs[dep]; found {
			if _, exists := targetFile.Structs[dep]; !exists {
				targetFile.Structs[dep] = s
			}
		}
		if c, found := parentVF.Classes[dep]; found {
			if _, exists := targetFile.Classes[dep]; !exists {
				targetFile.Classes[dep] = c
			}
		}
		if m, found := parentVF.Modules[dep]; found {
			if _, exists := targetFile.Modules[dep]; !exists {
				targetFile.Modules[dep] = m
			}
		}
		if i, found := parentVF.Interfaces[dep]; found {
			if _, exists := targetFile.Interfaces[dep]; !exists {
				targetFile.Interfaces[dep] = i
			}
		}
		if p, found := parentVF.Packages[dep]; found {
			if _, exists := targetFile.Packages[dep]; !exists {
				targetFile.Packages[dep] = p
			}
		}
		dfsDependencies(dep, parentVF, targetFile)
	}
}

func AddDependencies(targetFile *verilog.VerilogFile, snippet *Snippet) error {
	parentVF := snippet.ParentFile
	if parentVF == nil {
		return errors.New("snippet parent file is nil")
	}
	if targetFile.DependencyMap == nil {
		targetFile.DependencyMap = make(map[string]*verilog.DependencyNode)
	}
	if _, ok := targetFile.DependencyMap[snippet.Name]; !ok {
		targetFile.DependencyMap[snippet.Name] = &verilog.DependencyNode{
			Name:      snippet.Module.Name,
			DependsOn: []string{},
		}
	}
	targetFile.Modules[snippet.Module.Name] = snippet.Module

	dfsDependencies(snippet.Name, parentVF, targetFile)

	return nil
}
