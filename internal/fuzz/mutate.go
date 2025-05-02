package fuzz

import (
	"fmt"
	"path/filepath"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/utils"
)

var snippets = []string{}

func ExtractModules(filePath string) (map[string]string, error) {

	fileContent, err := utils.ReadFileContent(filePath)
	if err != nil {
		return nil, fmt.Errorf("failed to read file %s: %v", filePath, err)
	}
	fileName := filepath.Base(filePath)
	moduleName := ""

	lines := strings.Split(fileContent, "\n")
	allModules := make(map[string]string)
	moduleContent := []string{}

	for _, line := range lines {
		if strings.HasPrefix(line, "module") {
			moduleName = fileName + strings.TrimSpace(strings.Split(line, " ")[1])
			moduleContent = append(moduleContent, line)

		} else if strings.HasPrefix(line, "endmodule") {
			moduleContent = append(moduleContent, line)

			if moduleName != "" {
				allModules[moduleName] = strings.Join(moduleContent, "\n")
				moduleContent = []string{}
				moduleName = ""
			}

		} else if moduleName != "" {
			moduleContent = append(moduleContent, line)
		}
	}

	if len(allModules) == 0 {
		return nil, fmt.Errorf("no modules found in file %s", filePath)
	}

	return allModules, nil
}

func LoadSnippets() ([]string, error) {

	snippetsDir := filepath.Join("..", "..", "snippets")
	sourceFiles, err := filepath.Glob(filepath.Join(snippetsDir, "*.sv"))
	if err != nil {
		return nil, err
	}

	allModules := make(map[string]string)
	for _, snippetFile := range sourceFiles {
		modules, err := ExtractModules(snippetFile)
		if err != nil {
			return nil, err
		}
		for name, content := range modules {
			allModules[name] = content
		}
	}
	// Convert map to slice
	snippetList := make([]string, 0, len(allModules))
	for _, content := range allModules {
		snippetList = append(snippetList, content)
	}
	return snippetList, nil

}

func GetSnippets() ([]string, error) {
	if len(snippets) == 0 {
		var err error
		snippets, err = LoadSnippets()
		if err != nil {
			return nil, fmt.Errorf("failed to load snippets: %v", err)
		}
	}
	return snippets, nil
}

func GetRandomSnippet() (string, error) {
	snippets, err := GetSnippets()
	if err != nil {
		return "", fmt.Errorf("failed to get snippets: %v", err)
	}
	if len(snippets) == 0 {
		return "", fmt.Errorf("no snippets available")
	}
	randomIndex := utils.RandomInt(0, len(snippets)-1)
	return snippets[randomIndex], nil
}

func InjectSnippet(originalContent, snippet string) (string, error) {
	return "", fmt.Errorf("not implemented")
}

func MutateFile(fileName string, snippets []string) error {
	// Read the original file content
	originalContent, err := utils.ReadFileContent(fileName)
	if err != nil {
		return fmt.Errorf("failed to read file %s: %v", fileName, err)
	}
	// We are going to perform two kind of mutations :
	// 1. Inject a snippet at random in the file
	// 2. Add part of the code into a snippet

	// Write the mutated content back to the file
	utils.WriteFileContent(fileName, originalContent)
	return nil
}
