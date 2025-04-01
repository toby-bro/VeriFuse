package testgen

import (
	"fmt"
	"path/filepath"

	"github.com/jns/pfuzz/pkg/utils"
)

// Generator handles testbench generation
type Generator struct{}

// NewGenerator creates a new testbench generator
func NewGenerator() *Generator {
	return &Generator{}
}

// GenerateTestbenches creates both SystemVerilog and C++ testbenches
func (g *Generator) GenerateTestbenches() error {
	if err := g.GenerateSVTestbench(); err != nil {
		return fmt.Errorf("failed to generate SystemVerilog testbench: %v", err)
	}

	if err := g.GenerateCppTestbench(); err != nil {
		return fmt.Errorf("failed to generate C++ testbench: %v", err)
	}

	return nil
}

// GenerateSVTestbench creates the SystemVerilog testbench
func (g *Generator) GenerateSVTestbench() error {
	svTb := fmt.Sprintf(svTestbenchTemplate, utils.TMP_DIR, utils.TMP_DIR, utils.TMP_DIR, utils.TMP_DIR, utils.TMP_DIR)
	return utils.WriteFileContent(filepath.Join(utils.TMP_DIR, "testbench.sv"), svTb)
}

// GenerateCppTestbench creates the C++ testbench for Verilator
func (g *Generator) GenerateCppTestbench() error {
	cppTb := fmt.Sprintf(cppTestbenchTemplate, utils.TMP_DIR, utils.TMP_DIR, utils.TMP_DIR, utils.TMP_DIR, utils.TMP_DIR)
	return utils.WriteFileContent(filepath.Join(utils.TMP_DIR, "testbench.cpp"), cppTb)
}
