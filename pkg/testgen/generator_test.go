package testgen

import (
	"strings"
	"testing"

	"github.com/toby-bro/pfuzz/pkg/verilog"
)

// TestIsClockOrResetPort tests the helper function
func TestIsClockOrResetPort(t *testing.T) {
	clockPorts := []*verilog.Port{
		{Name: "clk"},
		{Name: "clock"},
	}
	resetPorts := []*verilog.Port{
		{Name: "rst"},
		{Name: "reset"},
	}

	tests := []struct {
		name     string
		portName string
		want     bool
	}{
		{"clock port clk", "clk", true},
		{"clock port clock", "clock", true},
		{"reset port rst", "rst", true},
		{"reset port reset", "reset", true},
		{"regular port data", "data", false},
		{"regular port enable", "enable", false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := isClockOrResetPort(tt.portName, clockPorts, resetPorts)
			if got != tt.want {
				t.Errorf("isClockOrResetPort(%q) = %v, want %v", tt.portName, got, tt.want)
			}
		})
	}
}

// TestCXXRTLInputDeclarationsSkipsClockReset tests that clock/reset are not declared as inputs
func TestCXXRTLInputDeclarationsSkipsClockReset(t *testing.T) {
	module := &verilog.Module{
		Name: "test_module",
		Ports: []*verilog.Port{
			{Name: "clk", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
			{Name: "rst", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
			{Name: "data_in", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 8},
			{Name: "data_out", Direction: verilog.OUTPUT, Type: verilog.LOGIC, Width: 8},
		},
	}

	gen := NewGenerator(module, "test_module.sv", nil)
	declarations := gen.generateCXXRTLInputDeclarations()

	// Check that data_in is declared
	if !strings.Contains(declarations, "data_in") {
		t.Error("Expected data_in to be declared, but it was not found")
	}

	// Check that clk is NOT declared
	if strings.Contains(declarations, "clk") {
		t.Error("Expected clk to NOT be declared, but it was found")
	}

	// Check that rst is NOT declared
	if strings.Contains(declarations, "rst") {
		t.Error("Expected rst to NOT be declared, but it was found")
	}
}

// TestCXXRTLInputReadsSkipsClockReset tests that clock/reset input files are not read
func TestCXXRTLInputReadsSkipsClockReset(t *testing.T) {
	module := &verilog.Module{
		Name: "test_module",
		Ports: []*verilog.Port{
			{Name: "clk", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
			{Name: "rst", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
			{Name: "data_in", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 8},
			{Name: "data_out", Direction: verilog.OUTPUT, Type: verilog.LOGIC, Width: 8},
		},
	}

	gen := NewGenerator(module, "test_module.sv", nil)
	inputReads := gen.generateCXXRTLInputReads()

	// Check that data_in file is read
	if !strings.Contains(inputReads, "input_data_in.hex") {
		t.Error("Expected input_data_in.hex to be read, but it was not found")
	}

	// Check that clk file is NOT read
	if strings.Contains(inputReads, "input_clk.hex") {
		t.Error("Expected input_clk.hex to NOT be read, but it was found")
	}

	// Check that rst file is NOT read
	if strings.Contains(inputReads, "input_rst.hex") {
		t.Error("Expected input_rst.hex to NOT be read, but it was found")
	}
}

// TestCXXRTLInputApplySkipsClockReset tests that clock/reset are not applied as regular inputs
func TestCXXRTLInputApplySkipsClockReset(t *testing.T) {
	module := &verilog.Module{
		Name: "test_module",
		Ports: []*verilog.Port{
			{Name: "clk", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
			{Name: "rst", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
			{Name: "data_in", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 8},
			{Name: "data_out", Direction: verilog.OUTPUT, Type: verilog.LOGIC, Width: 8},
		},
	}

	gen := NewGenerator(module, "test_module.sv", nil)
	inputApply := gen.generateCXXRTLInputApply("test_module_i")

	// Check that data_in is applied
	if !strings.Contains(inputApply, "p_data__in") {
		t.Error("Expected p_data__in to be applied, but it was not found")
	}

	// Check that clk is NOT applied
	if strings.Contains(inputApply, "p_clk") {
		t.Error("Expected p_clk to NOT be applied as regular input, but it was found")
	}

	// Check that rst is NOT applied
	if strings.Contains(inputApply, "p_rst") {
		t.Error("Expected p_rst to NOT be applied as regular input, but it was found")
	}
}

// TestCXXRTLResetLogicUsesSetPortValue tests that reset logic uses _set_port_value, not direct .set
func TestCXXRTLResetLogicUsesSetPortValue(t *testing.T) {
	module := &verilog.Module{
		Name: "test_module",
		Ports: []*verilog.Port{
			{Name: "rst", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
		},
	}

	gen := NewGenerator(module, "test_module.sv", nil)

	tests := []struct {
		name         string
		isActiveHigh bool
	}{
		{"active high reset", true},
		{"active low reset", false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			resetLogic := gen.generateCXXRTLResetLogic("dut", "rst", tt.isActiveHigh)

			// Check that _set_port_value is used
			if !strings.Contains(resetLogic, "_set_port_value<bool>") {
				t.Error("Expected _set_port_value<bool> to be used, but it was not found")
			}

			// Check that direct .set<bool> is NOT used
			if strings.Contains(resetLogic, ".p_rst.set<bool>") {
				t.Error("Expected direct .set<bool>() to NOT be used, but it was found")
			}

			// Check that the reset port is accessed correctly
			if !strings.Contains(resetLogic, "p_rst") {
				t.Error("Expected p_rst (mangled port name) to be used")
			}
		})
	}
}

// TestCXXRTLClockLogicUsesSetPortValue tests that clock logic uses _set_port_value
func TestCXXRTLClockLogicUsesSetPortValue(t *testing.T) {
	module := &verilog.Module{
		Name: "test_module",
		Ports: []*verilog.Port{
			{Name: "clk", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
			{Name: "data", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 8},
		},
	}

	gen := NewGenerator(module, "test_module.sv", nil)

	clockPorts := []*verilog.Port{
		{Name: "clk", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
	}

	clockLogic := gen.generateCXXRTLClockLogic("dut", clockPorts)

	// Check that _set_port_value is used for clock
	if !strings.Contains(clockLogic, "_set_port_value") {
		t.Error("Expected _set_port_value to be used for clock, but it was not found")
	}

	// Check that the clock port is accessed correctly
	if !strings.Contains(clockLogic, "p_clk") {
		t.Error("Expected p_clk (mangled port name) to be used")
	}

	// Check for bounded loop
	if !strings.Contains(clockLogic, "for (int cycle = 0; cycle <") {
		t.Error("Expected bounded clock loop, but it was not found")
	}
}

// TestCXXRTLTestbenchNoMixedAPIs is an integration test
func TestCXXRTLTestbenchNoMixedAPIs(t *testing.T) {
	module := &verilog.Module{
		Name: "counter",
		Ports: []*verilog.Port{
			{Name: "clk", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
			{Name: "rst", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
			{Name: "enable", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
			{Name: "count", Direction: verilog.OUTPUT, Type: verilog.LOGIC, Width: 8},
		},
	}

	gen := NewGenerator(module, "counter.sv", nil)

	// Generate all parts
	declarations := gen.generateCXXRTLInputDeclarations()
	inputReads := gen.generateCXXRTLInputReads()
	inputApply := gen.generateCXXRTLInputApply("counter_i")

	clockPorts, resetPorts, isActiveHigh := verilog.IdentifyClockAndResetPorts(module)

	var resetName string
	if len(resetPorts) > 0 {
		resetName = resetPorts[0].Name
	}

	resetLogic := gen.generateCXXRTLResetLogic("counter_i", resetName, isActiveHigh)
	clockLogic := gen.generateCXXRTLClockLogic("counter_i", clockPorts)

	// Combine all code
	allCode := declarations + inputReads + inputApply + resetLogic + clockLogic

	// Verify no input files for clock/reset
	if strings.Contains(allCode, "input_clk.hex") {
		t.Error("Found input_clk.hex in generated code, should be skipped")
	}
	if strings.Contains(allCode, "input_rst.hex") {
		t.Error("Found input_rst.hex in generated code, should be skipped")
	}

	// Verify clock/reset are not declared as input variables
	lines := strings.Split(declarations, "\n")
	for _, line := range lines {
		if strings.Contains(line, "bool clk") || strings.Contains(line, "uint8_t clk") {
			t.Error("Found clk declared as input variable, should be skipped")
		}
		if strings.Contains(line, "bool rst") || strings.Contains(line, "uint8_t rst") {
			t.Error("Found rst declared as input variable, should be skipped")
		}
	}

	// Verify enable (regular input) is handled correctly
	if !strings.Contains(allCode, "input_enable.hex") {
		t.Error("Expected input_enable.hex for regular input")
	}
	if !strings.Contains(declarations, "enable") {
		t.Error("Expected enable to be declared")
	}

	// Verify _set_port_value is used consistently (no direct .set calls)
	directSetPattern := ".set<bool>("
	if strings.Contains(allCode, directSetPattern) {
		t.Errorf("Found direct .set<bool>() call, should use _set_port_value instead")
	}
}

// TestMultipleClockPorts tests handling of multiple clock ports
func TestMultipleClockPorts(t *testing.T) {
	module := &verilog.Module{
		Name: "dual_clock",
		Ports: []*verilog.Port{
			{Name: "clk1", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
			{Name: "clk2", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
			{Name: "data", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 8},
		},
	}

	gen := NewGenerator(module, "dual_clock.sv", nil)

	clockPorts := []*verilog.Port{
		{Name: "clk1", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
		{Name: "clk2", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 1},
	}

	declarations := gen.generateCXXRTLInputDeclarations()
	inputReads := gen.generateCXXRTLInputReads()
	clockLogic := gen.generateCXXRTLClockLogic("dut", clockPorts)

	// Both clocks should be skipped in declarations and input reads
	if strings.Contains(declarations, "clk1") || strings.Contains(declarations, "clk2") {
		t.Error("Clock ports should not be in declarations")
	}
	if strings.Contains(inputReads, "input_clk1.hex") ||
		strings.Contains(inputReads, "input_clk2.hex") {
		t.Error("Clock input files should not be read")
	}

	// Both clocks should be in clock logic
	if !strings.Contains(clockLogic, "p_clk1") {
		t.Error("Expected p_clk1 in clock logic")
	}
	if !strings.Contains(clockLogic, "p_clk2") {
		t.Error("Expected p_clk2 in clock logic")
	}

	// Data should be handled normally
	if !strings.Contains(declarations, "data") {
		t.Error("Expected data in declarations")
	}
	if !strings.Contains(inputReads, "input_data.hex") {
		t.Error("Expected input_data.hex to be read")
	}
}

// TestNoClockOrReset tests module with no clock or reset
func TestNoClockOrReset(t *testing.T) {
	module := &verilog.Module{
		Name: "combinational",
		Ports: []*verilog.Port{
			{Name: "a", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 8},
			{Name: "b", Direction: verilog.INPUT, Type: verilog.LOGIC, Width: 8},
			{Name: "sum", Direction: verilog.OUTPUT, Type: verilog.LOGIC, Width: 8},
		},
	}

	gen := NewGenerator(module, "combinational.sv", nil)

	declarations := gen.generateCXXRTLInputDeclarations()
	inputReads := gen.generateCXXRTLInputReads()
	resetLogic := gen.generateCXXRTLResetLogic("dut", "", false)
	clockLogic := gen.generateCXXRTLClockLogic("dut", nil)

	// All inputs should be declared and read
	if !strings.Contains(declarations, "a") || !strings.Contains(declarations, "b") {
		t.Error("Expected all inputs to be declared")
	}
	if !strings.Contains(inputReads, "input_a.hex") ||
		!strings.Contains(inputReads, "input_b.hex") {
		t.Error("Expected all input files to be read")
	}

	// Reset logic should be empty
	if resetLogic != "" {
		t.Error("Expected empty reset logic for module without reset")
	}

	// Clock logic should still do settling steps
	if !strings.Contains(clockLogic, "settle") {
		t.Error("Expected settling steps even without clock")
	}
}
