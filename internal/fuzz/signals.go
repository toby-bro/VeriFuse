package fuzz

import (
	"strings"

	"github.com/toby-bro/pfuzz/internal/verilog"
)

// SignalType represents different types of signals for specialized handling
type SignalType int

const (
	SIGNAL_NORMAL SignalType = iota
	SIGNAL_CLOCK
	SIGNAL_RESET
	SIGNAL_VALID
	SIGNAL_READY
	SIGNAL_DATA
	SIGNAL_ADDRESS
	SIGNAL_OPCODE
	SIGNAL_CONTROL
	SIGNAL_ENUM
)

// SignalConstraint defines constraints for fuzzing a signal
type SignalConstraint struct {
	Type         SignalType
	FuzzWeight   float64                      // 0.0-1.0 (higher = fuzzed more often)
	DefaultValue string                       // Default value when not fuzzing
	ValidValues  []string                     // List of valid values (if applicable)
	DependsOn    string                       // Signal that this depends on
	DependencyFn func(map[string]string) bool // Function to check dependency
}

// SignalFamily represents broader categories of related signal types
type SignalFamily int

const (
	FAMILY_CONTROL SignalFamily = iota
	FAMILY_DATA
	FAMILY_TIMING
	FAMILY_STATE
)

// SignalRelationship tracks dependencies between signals
type SignalRelationship struct {
	SourceSignal      string
	DependentSignal   string
	RelationshipType  string // "enables", "validates", "selects", etc.
	ConstraintFormula string // Logical formula describing the constraint
}

// SignalUsageStats tracks statistical information about signal usage
type SignalUsageStats struct {
	MismatchRate      float64        // How often this signal appears in mismatches
	ToggleRate        float64        // How often the signal changes value
	ValueDistribution map[string]int // Distribution of observed values
}

// ClassifySignals analyzes module ports and returns signal constraints
func ClassifySignals(module *verilog.Module) map[string]SignalConstraint {
	constraints := make(map[string]SignalConstraint)

	for _, port := range module.Ports {
		if port.Direction != verilog.INPUT && port.Direction != verilog.INOUT {
			continue
		}

		portName := strings.TrimSpace(port.Name)
		portNameLower := strings.ToLower(portName)

		// Default constraint values
		constraint := SignalConstraint{
			Type:         SIGNAL_NORMAL,
			FuzzWeight:   1.0,
			DefaultValue: "0",
		}

		// Classify based on name patterns
		switch {
		case strings.Contains(portNameLower, "clk") || strings.Contains(portNameLower, "clock"):
			constraint.Type = SIGNAL_CLOCK
			constraint.FuzzWeight = 0.1 // Rarely fuzz clocks
			constraint.DefaultValue = "0"

		case strings.Contains(portNameLower, "rst") || strings.Contains(portNameLower, "reset"):
			constraint.Type = SIGNAL_RESET
			constraint.FuzzWeight = 0.2
			if strings.HasSuffix(portNameLower, "_n") || strings.HasSuffix(portNameLower, "_l") {
				constraint.DefaultValue = "1" // Active low reset
			} else {
				constraint.DefaultValue = "0" // Active high reset
			}

		case strings.Contains(portNameLower, "valid"):
			constraint.Type = SIGNAL_VALID
			constraint.FuzzWeight = 0.8
			constraint.DefaultValue = "0"

		case strings.Contains(portNameLower, "ready"):
			constraint.Type = SIGNAL_READY
			constraint.FuzzWeight = 0.7
			constraint.DefaultValue = "1"

		case strings.Contains(portNameLower, "data") || strings.Contains(portNameLower, "rdata") ||
			strings.Contains(portNameLower, "wdata"):
			constraint.Type = SIGNAL_DATA
			constraint.FuzzWeight = 0.9
			constraint.DefaultValue = "0"

		case strings.Contains(portNameLower, "addr"):
			constraint.Type = SIGNAL_ADDRESS
			constraint.FuzzWeight = 0.8
			constraint.DefaultValue = "0"

		case strings.Contains(portNameLower, "opcode") || strings.Contains(portNameLower, "instr"):
			constraint.Type = SIGNAL_OPCODE
			constraint.FuzzWeight = 0.9
			constraint.DefaultValue = "0"

		case strings.Contains(portNameLower, "sel") || strings.Contains(portNameLower, "mode") ||
			strings.Contains(portNameLower, "en") || strings.Contains(portNameLower, "cmd"):
			constraint.Type = SIGNAL_CONTROL
			constraint.FuzzWeight = 0.7
			constraint.DefaultValue = "0"

		// Special case for ibex_decoder ports
		case portName == "fetch_rdata_i":
			constraint.Type = SIGNAL_OPCODE
			constraint.FuzzWeight = 0.95
			constraint.DefaultValue = "0"

		case portName == "branch_taken_i":
			constraint.Type = SIGNAL_CONTROL
			constraint.FuzzWeight = 0.8
			constraint.DefaultValue = "0"

		// For enum types (determined from port width)
		case port.Width <= 4 && port.Width > 1:
			constraint.Type = SIGNAL_ENUM
			constraint.FuzzWeight = 0.8
			constraint.DefaultValue = "0"
		}

		constraints[portName] = constraint
	}

	return constraints
}

// EnhanceSignalConstraints adds advanced signal relationship information
// to the existing constraint classification
func EnhanceSignalConstraints(
	constraints map[string]SignalConstraint,
	module *verilog.Module,
) map[string]SignalConstraint {
	// Clone the constraints to avoid modifying the original
	enhanced := make(map[string]SignalConstraint)
	for k, v := range constraints {
		enhanced[k] = v
	}

	// Track signals that are likely part of protocol pairs (req/resp, valid/ready)
	protocolPairs := detectProtocolPairs(module)

	// Apply protocol-aware constraints
	for sourceName, targetName := range protocolPairs {
		if source, exists := enhanced[sourceName]; exists {
			// Make protocol initiator signals more likely to be toggled
			source.FuzzWeight = 0.9
			enhanced[sourceName] = source
		}

		if target, exists := enhanced[targetName]; exists {
			// For handshake protocols, the target usually starts ready
			if strings.Contains(strings.ToLower(targetName), "ready") {
				target.DefaultValue = "1"
			}
			enhanced[targetName] = target
		}
	}

	// Add dependency functions for valid/data relationships
	for portName, constraint := range enhanced {
		if constraint.Type == SIGNAL_VALID {
			// Add dependencies to corresponding data ports
			dataPortName := findCorrespondingDataPort(portName, module)
			if dataPortName != "" && dataPortName != portName {
				c := constraint // Create local copy to avoid loop variable issues
				c.DependsOn = dataPortName
				c.DependencyFn = func(inputs map[string]string) bool {
					// Only set valid if there's non-zero data
					dataVal, exists := inputs[dataPortName]
					return exists && dataVal != "0"
				}
				enhanced[portName] = c
			}
		}
	}

	// Add module-specific optimizations
	if strings.Contains(strings.ToLower(module.Name), "branch_predict") {
		// For branch predictors, generate more realistic instruction streams
		if fetchValid, exists := enhanced["fetch_valid_i"]; exists {
			fetchValid.DependencyFn = func(inputs map[string]string) bool {
				// Don't assert valid unless we have reasonable instruction data
				if rdata, ok := inputs["fetch_rdata_i"]; ok && rdata != "0" {
					return true
				}
				return false
			}
			enhanced["fetch_valid_i"] = fetchValid
		}
	}

	return enhanced
}

// detectProtocolPairs finds likely protocol handshake pairs
func detectProtocolPairs(module *verilog.Module) map[string]string {
	pairs := make(map[string]string)

	// Identify valid/ready pairs
	validSignals := make([]string, 0)
	readySignals := make([]string, 0)

	for _, port := range module.Ports {
		name := strings.ToLower(port.Name)
		if strings.Contains(name, "valid") &&
			(port.Direction == verilog.INPUT || port.Direction == verilog.INOUT) {
			validSignals = append(validSignals, port.Name)
		}
		if strings.Contains(name, "ready") {
			readySignals = append(readySignals, port.Name)
		}
	}

	// Match valid signals with corresponding ready signals
	for _, valid := range validSignals {
		validLower := strings.ToLower(valid)
		for _, ready := range readySignals {
			readyLower := strings.ToLower(ready)

			// Match by prefix/suffix patterns
			if strings.Replace(validLower, "valid", "", 1) ==
				strings.Replace(readyLower, "ready", "", 1) {
				pairs[valid] = ready
				break
			}
		}
	}

	return pairs
}

// findCorrespondingDataPort tries to find the data port that corresponds to a valid signal
func findCorrespondingDataPort(validPortName string, module *verilog.Module) string {
	// Common patterns: xxx_valid -> xxx_data, instr_valid_i -> instr_rdata_i
	validBase := strings.Replace(strings.ToLower(validPortName), "valid", "", 1)
	validBase = strings.TrimSuffix(validBase, "_i")
	validBase = strings.TrimSuffix(validBase, "_o")

	for _, port := range module.Ports {
		portNameLower := strings.ToLower(port.Name)
		if strings.Contains(portNameLower, "data") && strings.Contains(portNameLower, validBase) {
			return port.Name
		}

		// Special case for instruction ports
		if strings.Contains(validPortName, "instr") &&
			(strings.Contains(port.Name, "rdata") || strings.Contains(port.Name, "instr")) {
			return port.Name
		}
	}

	return "" // No matching data port found
}

// GetSignalFamily determines the broader functional family of a signal
func GetSignalFamily(constraint SignalConstraint) SignalFamily {
	switch constraint.Type {
	case SIGNAL_VALID, SIGNAL_READY, SIGNAL_CONTROL, SIGNAL_ENUM:
		return FAMILY_CONTROL
	case SIGNAL_DATA, SIGNAL_ADDRESS, SIGNAL_OPCODE:
		return FAMILY_DATA
	case SIGNAL_CLOCK, SIGNAL_RESET:
		return FAMILY_TIMING
	case SIGNAL_NORMAL:
		return FAMILY_STATE
	default:
		return FAMILY_STATE
	}
}
