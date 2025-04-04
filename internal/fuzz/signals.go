package fuzz

import (
	"strings"

	"github.com/toby-bro/pfuzz/internal/verilog"
)

// SignalType represents classification of an input signal
type SignalType int

const (
	SIGNAL_NORMAL SignalType = iota // Normal signal that can be fuzzed freely
	SIGNAL_CLOCK                    // Clock signal that should toggle
	SIGNAL_RESET                    // Reset signal
	SIGNAL_VALID                    // Valid/enable signal
	SIGNAL_SELECT                   // Selection signal (e.g. mux select)
)

// SignalConstraint defines special handling for input signals
type SignalConstraint struct {
	Type          SignalType
	DefaultValue  string
	DependentOn   []string // List of signals this depends on
	AllowedValues []string // Specific allowed values
	FuzzWeight    float64  // How often to fuzz this (0-1)
}

// ClassifySignals categorizes module signals based on naming conventions
func ClassifySignals(module *verilog.Module) map[string]SignalConstraint {
	constraints := make(map[string]SignalConstraint)

	for _, port := range module.Ports {
		if port.Direction != verilog.INPUT {
			continue
		}

		name := strings.ToLower(port.Name)

		// Classify based on naming conventions
		switch {
		case strings.Contains(name, "clk") || strings.Contains(name, "clock"):
			constraints[port.Name] = SignalConstraint{
				Type:         SIGNAL_CLOCK,
				DefaultValue: "0", // Start with clock low
				FuzzWeight:   0.5, // Allow the clock to be fuzzed to test initial state, but toggling is handled by testbenches
			}

		case strings.Contains(name, "rst") || strings.Contains(name, "reset"):
			constraints[port.Name] = SignalConstraint{
				Type:         SIGNAL_RESET,
				DefaultValue: "1", // Usually active-low reset (deasserted)
				FuzzWeight:   0.1, // Rarely fuzz reset
			}

		case strings.Contains(name, "valid") || strings.Contains(name, "enable"):
			// Valid signals should be checked against dependent data signals
			constraints[port.Name] = SignalConstraint{
				Type:         SIGNAL_VALID,
				DefaultValue: "0", // Default to not valid
				FuzzWeight:   0.3, // Fuzz sometimes, but controlled
			}

		case strings.Contains(name, "sel") || strings.Contains(name, "select"):
			constraints[port.Name] = SignalConstraint{
				Type:         SIGNAL_SELECT,
				DefaultValue: "0",
				FuzzWeight:   0.8, // Fuzz frequently
			}

		default:
			constraints[port.Name] = SignalConstraint{
				Type:         SIGNAL_NORMAL,
				DefaultValue: "0",
				FuzzWeight:   1.0, // Always fuzz
			}
		}
	}

	return constraints
}
