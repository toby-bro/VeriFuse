package snippets

import (
	"errors"
	"fmt"

	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

func (s *Snippet) writeSnippetToFile() error {
	if s.Module == nil {
		return errors.New("module is nil")
	}
	if s.ParentFile == nil {
		return errors.New("parent file is nil")
	}

	baseName := s.ParentFile.Name
	if len(baseName) > 3 && baseName[len(baseName)-3:] == ".sv" {
		baseName = baseName[:len(baseName)-3]
	}

	svFile := verilog.NewVerilogFile(s.Module.Name + ".sv")

	err := AddDependencies(svFile, s)
	if err != nil {
		return fmt.Errorf("failed to add dependencies: %v", err)
	}
	content, err := verilog.PrintVerilogFile(svFile)
	if err != nil {
		return fmt.Errorf("failed to print Verilog file: %v", err)
	}
	path, err := utils.GetRootDir()
	if err != nil {
		return fmt.Errorf("failed to get root directory: %v", err)
	}
	filePath := path + "/isolated/" + baseName
	err = utils.EnsureDirWithPath(filePath)
	if err != nil {
		return fmt.Errorf("failed to create directory for Verilog file: %v", err)
	}
	err = utils.WriteFileContent(filePath+"/"+svFile.Name, content)
	if err != nil {
		return fmt.Errorf("failed to write Verilog file: %v", err)
	}
	return nil
}

func splitVerilogFile(svFile *verilog.VerilogFile) ([]*Snippet, error) {
	if svFile == nil {
		return nil, errors.New("Verilog file is nil")
	}
	snippets := []*Snippet{}
	for _, module := range svFile.Modules {
		snippet := &Snippet{
			Name:       module.Name,
			Module:     module,
			ParentFile: svFile,
		}
		snippets = append(snippets, snippet)
	}
	return snippets, nil
}

func writeSnippetsToFile(snippets []*Snippet) error {
	for _, snippet := range snippets {
		err := snippet.writeSnippetToFile()
		if err != nil {
			return fmt.Errorf("failed to write snippet to file: %v", err)
		}
	}
	return nil
}

func WriteFileAsSnippets(svFile *verilog.VerilogFile) error {
	snippets, err := splitVerilogFile(svFile)
	if err != nil {
		return fmt.Errorf("failed to split Verilog file: %v", err)
	}
	err = writeSnippetsToFile(snippets)
	if err != nil {
		return fmt.Errorf("failed to write snippets to file: %v", err)
	}
	return nil
}
