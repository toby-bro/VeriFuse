package fuzz

import (
	"fmt"
	"math/rand"
	"strings"

	"github.com/jns/pfuzz/internal/verilog"
)

// Strategy defines an interface for different fuzzing strategies
type Strategy interface {
	GenerateTestCase(iteration int) map[string]string
	Name() string
}

// ModuleAwareStrategy is an optional interface for strategies that need module info
type ModuleAwareStrategy interface {
	SetModule(module *verilog.Module)
}

// GenerateHexValue generates a random hex value of the appropriate width for a port
func GenerateHexValue(width int, r *rand.Rand) string {
	// Calculate number of hex digits needed (ceiling of width/4)
	hexDigits := (width + 3) / 4

	// For debug validation
	if width == 32 && hexDigits != 8 {
		hexDigits = 8 // Force correction for 32-bit values
	}

	// For 32-bit values, generate a full range of interesting values
	if width == 32 {
		strategy := r.Intn(10)
		switch strategy {
		case 0: // All zeros
			return "00000000"
		case 1: // All ones
			return "ffffffff"
		case 2: // Single bit set in high word
			bitPos := 16 + r.Intn(16)
			value := uint64(1) << bitPos
			return fmt.Sprintf("%08x", value)
		case 3: // Single bit set in low word
			bitPos := r.Intn(16)
			value := uint64(1) << bitPos
			return fmt.Sprintf("%08x", value)
		case 4: // Alternating bits
			return "55555555"
		case 5: // Inverse alternating bits
			return "aaaaaaaa"
		case 6: // Small positive number
			return fmt.Sprintf("%08x", r.Intn(1000))
		case 7: // Likely address (aligned)
			// Generate address-like pattern (e.g., 0x00004000)
			value := uint64(r.Intn(0x10)) << 12
			return fmt.Sprintf("%08x", value)
		case 8: // Special pattern
			patterns := []string{"deadbeef", "cafebabe", "a5a5a5a5", "01234567", "fedcba98"}
			return patterns[r.Intn(len(patterns))]
		default: // Fully random value
			value := r.Uint64() & 0xFFFFFFFF
			return fmt.Sprintf("%08x", value)
		}
	}

	// Generate random value with appropriate range
	maxValue := uint64(1)
	for i := 0; i < width; i++ {
		maxValue *= 2
	}
	maxValue-- // Get 2^width - 1

	// Limit to 64 bits max (uint64 range)
	if width > 64 {
		hexDigits = 16 // Max 16 hex digits for 64-bit
		maxValue = 0xFFFFFFFFFFFFFFFF
	}

	value := r.Uint64() % maxValue

	// Format with the right number of hex digits
	return fmt.Sprintf("%0*x", hexDigits, value)
}

// SimpleStrategy implements a simple random testing strategy
type SimpleStrategy struct {
	seed   int64
	module *verilog.Module
}

func (s *SimpleStrategy) SetModule(module *verilog.Module) {
	s.module = module
}

func (s *SimpleStrategy) Name() string {
	return "simple"
}

func (s *SimpleStrategy) GenerateTestCase(iteration int) map[string]string {
	r := rand.New(rand.NewSource(s.seed + int64(iteration)))

	// Create a map for all input values
	testCase := make(map[string]string)

	if s.module == nil {
		return testCase
	}

	// Generate values for all input ports
	for _, port := range s.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			if port.Width == 1 {
				// For single-bit ports, generate 0 or 1
				testCase[port.Name] = fmt.Sprintf("%d", r.Intn(2))
			} else {
				// For other multi-bit ports, generate appropriate width hex value
				testCase[port.Name] = GenerateHexValue(port.Width, r)
			}
		}
	}

	return testCase
}

// RandomStrategy implements a more sophisticated random strategy
type RandomStrategy struct {
	seed   int64
	module *verilog.Module
}

func (s *RandomStrategy) SetModule(module *verilog.Module) {
	s.module = module
}

func (s *RandomStrategy) Name() string {
	return "random"
}

func (s *RandomStrategy) GenerateTestCase(iteration int) map[string]string {
	r := rand.New(rand.NewSource(s.seed + int64(iteration)))

	// Create a map for all input values
	testCase := make(map[string]string)

	if s.module == nil {
		return testCase
	}

	// Generate values for all input ports
	for _, port := range s.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			if port.Width == 1 {
				// For single-bit ports
				testCase[port.Name] = fmt.Sprintf("%d", r.Intn(2))
			} else {
				// For multi-bit ports, use different strategies
				strategy := r.Intn(5)
				switch strategy {
				case 0: // All zeros
					testCase[port.Name] = "0"
				case 1: // All ones - with proper width
					hexDigits := (port.Width + 3) / 4
					testCase[port.Name] = strings.Repeat("f", hexDigits)
				case 2: // Single bit set
					bitPos := r.Intn(port.Width)
					value := uint64(1) << bitPos
					hexDigits := (port.Width + 3) / 4
					testCase[port.Name] = fmt.Sprintf("%0*x", hexDigits, value)
				case 3: // Alternating bits
					pattern := uint64(0)
					for i := 0; i < port.Width && i < 64; i += 2 {
						pattern |= (uint64(1) << i)
					}
					hexDigits := (port.Width + 3) / 4
					testCase[port.Name] = fmt.Sprintf("%0*x", hexDigits, pattern)
				default: // Random value with proper width
					testCase[port.Name] = GenerateHexValue(port.Width, r)
				}
			}
		}
	}

	return testCase
}

// SmartStrategy implements a context-aware fuzzing strategy
type SmartStrategy struct {
	seed         int64
	module       *verilog.Module
	previousRuns []map[string]string
	constraints  map[string]SignalConstraint
}

func (s *SmartStrategy) SetModule(module *verilog.Module) {
	s.module = module
	// Add signal classification
	s.constraints = ClassifySignals(module)
}

func (s *SmartStrategy) Name() string {
	return "smart"
}

func (s *SmartStrategy) GenerateTestCase(iteration int) map[string]string {
	r := rand.New(rand.NewSource(s.seed + int64(iteration)))

	// Create a map for all input values
	testCase := make(map[string]string)

	if s.module == nil {
		return testCase
	}

	// If we have previous runs, sometimes mutate one of them
	if len(s.previousRuns) > 5 && r.Intn(4) == 0 {
		baseCase := s.previousRuns[r.Intn(len(s.previousRuns))]

		// Copy the base case
		for k, v := range baseCase {
			testCase[k] = v
		}

		// Mutate a random input
		for _, port := range s.module.Ports {
			if (port.Direction == verilog.INPUT || port.Direction == verilog.INOUT) && r.Intn(4) == 0 {
				if port.Width == 1 {
					// For single-bit ports, flip the bit
					if testCase[port.Name] == "0" {
						testCase[port.Name] = "1"
					} else {
						testCase[port.Name] = "0"
					}
				} else {
					// For multi-bit ports, alter a few bits
					var valueInt uint64
					fmt.Sscanf(testCase[port.Name], "%x", &valueInt)

					// Flip a random bit
					bitPos := r.Intn(port.Width)
					valueInt ^= (uint64(1) << bitPos)

					testCase[port.Name] = fmt.Sprintf("%x", valueInt)
				}
			}
		}
	} else {
		// Generate a new test case with smart values

		// Identify control-like and data-like signals
		controlPorts := make([]verilog.Port, 0)
		dataPorts := make([]verilog.Port, 0)

		for _, port := range s.module.Ports {
			if port.Direction != verilog.INPUT && port.Direction != verilog.INOUT {
				continue
			}

			// Classify ports based on naming and width
			name := strings.ToLower(port.Name)
			isControl := strings.Contains(name, "en") ||
				strings.Contains(name, "valid") ||
				strings.Contains(name, "ready") ||
				strings.Contains(name, "sel") ||
				strings.Contains(name, "mode") ||
				port.Width <= 4

			if isControl {
				controlPorts = append(controlPorts, port)
			} else {
				dataPorts = append(dataPorts, port)
			}
		}

		// Set control signals first
		for _, port := range controlPorts {
			if port.Width == 1 {
				// Higher likelihood of asserting control signals
				if r.Intn(4) > 0 {
					testCase[port.Name] = "1"
				} else {
					testCase[port.Name] = "0"
				}
			} else {
				// For small multi-bit control signals
				maxValue := uint64(1<<port.Width) - 1
				value := r.Uint64() % (maxValue + 1)
				testCase[port.Name] = fmt.Sprintf("%x", value)
			}
		}

		// Then set data signals
		for _, port := range dataPorts {
			strategy := r.Intn(8)
			switch strategy {
			case 0: // All zeros
				testCase[port.Name] = "0"
			case 1: // All ones
				hexDigits := (port.Width + 3) / 4
				testCase[port.Name] = strings.Repeat("f", hexDigits)
			case 2: // Single bit set
				bitPos := r.Intn(port.Width)
				value := uint64(1) << bitPos
				hexDigits := (port.Width + 3) / 4
				testCase[port.Name] = fmt.Sprintf("%0*x", hexDigits, value)
			case 3: // Alternating bits
				pattern := uint64(0)
				for i := 0; i < port.Width && i < 64; i += 2 {
					pattern |= (uint64(1) << i)
				}
				hexDigits := (port.Width + 3) / 4
				testCase[port.Name] = fmt.Sprintf("%0*x", hexDigits, pattern)
			case 4: // Small integer
				value := r.Intn(10)
				testCase[port.Name] = fmt.Sprintf("%x", value)
			case 5: // Powers of 2
				power := r.Intn(port.Width)
				value := uint64(1) << power
				testCase[port.Name] = fmt.Sprintf("%x", value)
			case 6: // Powers of 2 minus 1
				power := r.Intn(port.Width) + 1
				value := uint64((1 << power) - 1)
				testCase[port.Name] = fmt.Sprintf("%x", value)
			default: // Fully random value
				testCase[port.Name] = GenerateHexValue(port.Width, r)
			}
		}
	}

	// When generating values, respect constraints
	for _, port := range s.module.Ports {
		if port.Direction != verilog.INPUT && port.Direction != verilog.INOUT {
			continue
		}

		constraint, hasConstraint := s.constraints[port.Name]
		if !hasConstraint {
			constraint = SignalConstraint{
				Type:       SIGNAL_NORMAL,
				FuzzWeight: 1.0,
			}
		}

		// Decide whether to fuzz based on weight
		if r.Float64() > constraint.FuzzWeight {
			testCase[port.Name] = constraint.DefaultValue
			continue
		}

		// Special handling for valid signals - only set valid if data is set
		if constraint.Type == SIGNAL_VALID {
			// Ensure we're not setting fetch_valid_i=1 with invalid data
			// For the branch predictor specifically, we need valid instruction data
			if port.Name == "fetch_valid_i" && hasUsableInstruction(testCase) {
				testCase[port.Name] = "1" // OK to set valid
			} else {
				testCase[port.Name] = "0" // Keep invalid
			}
			continue
		}

		// For all other signals, generate appropriate values based on width
		if port.Width == 1 {
			testCase[port.Name] = fmt.Sprintf("%d", r.Intn(2))
		} else {
			// Use smarter generation with proper width
			strategy := r.Intn(8)
			switch strategy {
			case 0: // All zeros
				testCase[port.Name] = "0"
			case 1: // All ones
				hexDigits := (port.Width + 3) / 4
				testCase[port.Name] = strings.Repeat("f", hexDigits)
			case 2: // Single bit set
				bitPos := r.Intn(port.Width)
				value := uint64(1) << bitPos
				hexDigits := (port.Width + 3) / 4
				testCase[port.Name] = fmt.Sprintf("%0*x", hexDigits, value)
			case 3: // Alternating bits
				pattern := uint64(0)
				for i := 0; i < port.Width && i < 64; i += 2 {
					pattern |= (uint64(1) << i)
				}
				hexDigits := (port.Width + 3) / 4
				testCase[port.Name] = fmt.Sprintf("%0*x", hexDigits, pattern)
			default: // Fully random value
				testCase[port.Name] = GenerateHexValue(port.Width, r)
			}
		}
	}

	// Store this test case for future mutation
	if len(s.previousRuns) >= 20 {
		s.previousRuns = s.previousRuns[1:]
	}
	s.previousRuns = append(s.previousRuns, testCase)

	return testCase
}

// hasUsableInstruction checks if input values would form a valid instruction
func hasUsableInstruction(testCase map[string]string) bool {
	// This is module-specific logic - would need customization
	// For example, check if fetch_rdata_i has a sensible value

	// Simplistic version:
	if rdata, ok := testCase["fetch_rdata_i"]; ok && rdata != "0" {
		return true
	}
	return false
}
