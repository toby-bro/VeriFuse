package synth

import (
	"context"

	"github.com/toby-bro/pfuzz/pkg/utils"
)

// Type represents different synthesizer/transpiler types
type Type int

const (
	None Type = iota
	YOSYS
	SV2V
	VIVADO
	QUARTUS_SYNTH
	GENUS
)

// String returns the string representation of the synthesizer type
func (t Type) String() string {
	switch t {
	case None:
		return ""
	case YOSYS:
		return "Yosys"
	case SV2V:
		return "SV2V"
	case VIVADO:
		return "Vivado"
	case QUARTUS_SYNTH:
		return "Quartus Synthesis"
	case GENUS:
		return "Genus"
	default:
		return "Unknown"
	}
}

// Synthesizer defines the interface for synthesis tools
type Synthesizer interface {
	// Transform processes the input file and generates output
	Transform(ctx context.Context, moduleName, srcPath, outputPath string) error

	// Test checks if the synthesizer tool is available
	Test() error

	// Type returns the synthesizer type
	Type() Type
}

// TestAvailableSynthesizers returns a list of available synthesizer types
func TestAvailableSynthesizers(debugger *utils.DebugLogger) []Type {
	var available []Type

	if err := TestYosysTool(); err == nil {
		available = append(available, YOSYS)
	} else {
		debugger.Warn("Yosys tool not available: %v", err)
	}

	if err := TestSV2VTool(); err == nil {
		available = append(available, SV2V)
	} else {
		debugger.Warn("SV2V tool not available: %v", err)
	}

	if err := TestVivadoTool(); err == nil {
		available = append(available, VIVADO)
	} else {
		debugger.Warn("Vivado tool not available: %v", err)
	}

	return available
}
