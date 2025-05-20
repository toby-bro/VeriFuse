package snippets

import (
	"path/filepath"
	"testing"

	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

func TestWriteFileAsSnippets(t *testing.T) {
	t.Skip("Skipping test as not ran manually")
	rootDir, err := utils.GetRootDir()
	if err != nil {
		t.Fatalf("failed to get root directory: %v", err)
	}
	svFilePath := filepath.Join(rootDir, "snippets", "V3DepthBlock.sv")
	content, err := utils.ReadFileContent(svFilePath)
	if err != nil {
		t.Fatalf("failed to read file content: %v", err)
	}
	svFile, err := verilog.ParseVerilog(content, 5)
	if err != nil {
		t.Fatalf("failed to parse Verilog file: %v", err)
	}
	err = WriteFileAsSnippets(svFile)
	if err != nil {
		t.Fatalf("failed to write file as snippets: %v", err)
	}
}
