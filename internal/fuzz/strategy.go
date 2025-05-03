package fuzz

import (
	"fmt"
	"log"
	"math/rand"
	"strconv"
	"strings"

	"github.com/toby-bro/pfuzz/internal/verilog"
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
				testCase[port.Name] = strconv.Itoa(r.Intn(2))
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
				testCase[port.Name] = strconv.Itoa(r.Intn(2))
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
	// Use the enhanced signal constraints for smarter fuzzing
	baseConstraints := ClassifySignals(module)
	s.constraints = EnhanceSignalConstraints(baseConstraints, module)
}

func (s *SmartStrategy) Name() string {
	return "smart"
}

// mutateTestCase takes a base test case and mutates some inputs
func (s *SmartStrategy) mutateTestCase(baseCase map[string]string, r *rand.Rand) map[string]string {
	testCase := make(map[string]string)
	// Copy the base case
	for k, v := range baseCase {
		testCase[k] = v
	}

	// Mutate a random input
	for _, port := range s.module.Ports {
		if (port.Direction == verilog.INPUT || port.Direction == verilog.INOUT) &&
			r.Intn(4) == 0 { // Mutate with 25% probability
			if port.Width == 1 {
				// For single-bit ports, flip the bit
				if testCase[port.Name] == "0" {
					testCase[port.Name] = "1"
				} else {
					testCase[port.Name] = "0"
				}
			} else {
				// For multi-bit ports, alter a few bits (e.g., flip one bit)
				var valueInt uint64
				n, err := fmt.Sscanf(testCase[port.Name], "%x", &valueInt)
				if err != nil || n != 1 {
					log.Printf("Failed to parse hex value %s for mutation: %v", testCase[port.Name], err)
					// Fallback: generate a new random value if parsing fails
					testCase[port.Name] = GenerateHexValue(port.Width, r)
					continue
				}

				// Flip a random bit
				if port.Width > 0 {
					bitPos := r.Intn(port.Width)
					valueInt ^= (uint64(1) << bitPos)
				}

				// Ensure the value fits within the port width
				if port.Width < 64 {
					mask := (uint64(1) << port.Width) - 1
					valueInt &= mask
				}

				hexDigits := (port.Width + 3) / 4
				testCase[port.Name] = fmt.Sprintf("%0*x", hexDigits, valueInt)
			}
		}
	}
	return testCase
}

// generateControlPortValue generates a value for a control port
func (s *SmartStrategy) generateControlPortValue(port verilog.Port, r *rand.Rand) string {
	if port.Width == 1 {
		// Higher likelihood of asserting control signals (e.g., 75% chance of '1')
		if r.Intn(4) > 0 {
			return "1"
		}
		return "0"
	}
	// For small multi-bit control signals, generate a random value within the width
	var maxValue uint64 // Declare maxValue
	if port.Width < 64 {
		maxValue = uint64(1 << port.Width) // Assign inside if
	} else {
		// Handle 64-bit case where 1 << 64 overflows
		maxValue = 0 // Assign inside else (Effectively means use full uint64 range below)
	}

	var value uint64
	if maxValue > 0 {
		value = r.Uint64() % maxValue
	} else {
		value = r.Uint64() // Full 64-bit range
	}

	hexDigits := (port.Width + 3) / 4
	return fmt.Sprintf("%0*x", hexDigits, value)
}

// generateDataPortValue generates a value for a data port using various strategies
func (s *SmartStrategy) generateDataPortValue(port verilog.Port, r *rand.Rand) string {
	strategy := r.Intn(8) // Choose one of the 8 strategies
	hexDigits := (port.Width + 3) / 4

	switch strategy {
	case 0: // All zeros
		return "0"
	case 1: // All ones
		return strings.Repeat("f", hexDigits)
	case 2: // Single bit set
		if port.Width == 0 {
			return "0"
		}
		bitPos := r.Intn(port.Width)
		value := uint64(1) << bitPos
		return fmt.Sprintf("%0*x", hexDigits, value)
	case 3: // Alternating bits (0101...)
		pattern := uint64(0x5555555555555555)
		if port.Width < 64 {
			mask := (uint64(1) << port.Width) - 1
			pattern &= mask
		}
		return fmt.Sprintf("%0*x", hexDigits, pattern)
	case 4: // Small integer (0-9)
		value := r.Intn(10)
		return fmt.Sprintf("%x", value) // No zero padding needed for small numbers usually
	case 5: // Powers of 2
		if port.Width == 0 {
			return "0"
		}
		power := r.Intn(port.Width)
		value := uint64(1) << power
		return fmt.Sprintf("%0*x", hexDigits, value)
	case 6: // Powers of 2 minus 1 (all ones up to a point)
		if port.Width == 0 {
			return "0"
		}
		power := r.Intn(port.Width) + 1
		value := uint64((uint64(1) << power) - 1)
		return fmt.Sprintf("%0*x", hexDigits, value)
	default: // Fully random value using the existing helper
		return GenerateHexValue(port.Width, r)
	}
}

// generateNewTestCase creates a new test case from scratch using smart strategies
func (s *SmartStrategy) generateNewTestCase(r *rand.Rand) map[string]string {
	testCase := make(map[string]string)

	// Identify control-like and data-like signals
	controlPorts := make([]verilog.Port, 0)
	dataPorts := make([]verilog.Port, 0)

	for _, port := range s.module.Ports {
		if port.Direction != verilog.INPUT && port.Direction != verilog.INOUT {
			continue
		}

		// Classify ports based on naming and width (example criteria)
		name := strings.ToLower(port.Name)
		isControl := strings.Contains(name, "en") ||
			strings.Contains(name, "valid") ||
			strings.Contains(name, "ready") ||
			strings.Contains(name, "sel") ||
			strings.Contains(name, "mode") ||
			port.Width <= 4 // Treat narrow ports as control

		if isControl {
			controlPorts = append(controlPorts, port)
		} else {
			dataPorts = append(dataPorts, port)
		}
	}

	// Set control signals first
	for _, port := range controlPorts {
		testCase[port.Name] = s.generateControlPortValue(port, r)
	}

	// Then set data signals
	for _, port := range dataPorts {
		testCase[port.Name] = s.generateDataPortValue(port, r)
	}

	return testCase
}

// applyConstraints modifies the test case based on signal constraints
func (s *SmartStrategy) applyConstraints(testCase map[string]string, r *rand.Rand) {
	for _, port := range s.module.Ports {
		if port.Direction != verilog.INPUT && port.Direction != verilog.INOUT {
			continue
		}

		constraint, hasConstraint := s.constraints[port.Name]
		if !hasConstraint {
			// Apply default constraint if none found
			constraint = SignalConstraint{
				Type:       SIGNAL_NORMAL,
				FuzzWeight: 1.0, // Default to always fuzz if no constraint
			}
		}

		// Decide whether to skip fuzzing based on weight
		if r.Float64() > constraint.FuzzWeight {
			if constraint.DefaultValue != "" {
				testCase[port.Name] = constraint.DefaultValue
			} else {
				// If no default, generate a simple value (e.g., 0)
				testCase[port.Name] = "0"
			}
			continue // Skip further processing for this port
		}

		// Apply type-specific constraints
		switch constraint.Type {
		case SIGNAL_VALID:
			// Special handling for valid signals: only set valid if related data seems usable
			relatedDataPort := "" // Determine the related data port if possible
			isDataUsable := false // Default to false unless proven otherwise

			// Example: fetch_valid_i depends on fetch_rdata_i
			// This logic might need to be more sophisticated based on specific module interactions
			if strings.HasPrefix(port.Name, "fetch_valid") {
				relatedDataPort = "fetch_rdata_i"
				// Check if the related data port has a non-zero value
				if rdata, ok := testCase[relatedDataPort]; ok && rdata != "0" && rdata != "" {
					// Could add more checks here (e.g., instruction format validity)
					isDataUsable = true
				}
			} else {
				// If no specific related data port is known, assume data might be usable
				// or base it on other heuristics if needed. For now, default assumption.
				isDataUsable = true // Or keep false if a valid signal *always* needs specific data
			}
			// Add more rules for other valid signals and their dependencies as needed

			if isDataUsable {
				// If data is usable, allow valid signal to be potentially set (it might already be 1 or 0)
				// Re-generate a value respecting the original probability (e.g., 75% chance of 1 for control)
				if port.Width == 1 && r.Intn(4) > 0 {
					testCase[port.Name] = "1"
				} else if port.Width == 1 {
					testCase[port.Name] = "0"
				} // Keep existing multi-bit value if applicable
			} else {
				// If data is not usable, force valid signal to 0
				testCase[port.Name] = "0"
			}

		case SIGNAL_READY:
			// Ready signals often default high or are less critical to drive low initially
			// We might bias them towards '1'
			if port.Width == 1 && r.Intn(4) > 0 { // 75% chance of '1'
				testCase[port.Name] = "1"
			} else if port.Width == 1 {
				testCase[port.Name] = "0"
			} // Keep existing multi-bit value

		case SIGNAL_ADDRESS:
			// Generate address-like values (e.g., aligned, within certain ranges)
			// This could reuse parts of GenerateHexValue's 32-bit logic
			if port.Width == 32 { // Example for 32-bit address
				value := uint64(r.Intn(0x1000)) << r.Intn(5) // Generate somewhat aligned values
				testCase[port.Name] = fmt.Sprintf("%08x", value)
			} else {
				// Fallback for other widths
				testCase[port.Name] = GenerateHexValue(port.Width, r)
			}

		case SIGNAL_DATA:
			// No specific action needed here unless further constraints are added.

		case SIGNAL_CLOCK, SIGNAL_RESET:
			// Clocks and resets are usually handled by the testbench, not fuzzed directly.
			// If they *are* inputs here, they might need specific non-random values.
			// Often, they might have a FuzzWeight of 0.0 in constraints.
			// If fuzzing is enabled (weight > 0), treat as normal 1-bit signal for now.
			if port.Width == 1 {
				testCase[port.Name] = strconv.Itoa(r.Intn(2))
			} else {
				testCase[port.Name] = GenerateHexValue(port.Width, r) // Unlikely case
			}

		case SIGNAL_OPCODE:
			// TODO: Add specific handling for opcode signals if needed.
			// Falls through to default/normal handling for now.
			fallthrough
		case SIGNAL_CONTROL:
			// TODO: Add specific handling for general control signals if needed.
			// Falls through to default/normal handling for now.
			fallthrough
		case SIGNAL_ENUM:
			// TODO: Add specific handling for enum signals if needed (e.g., generate valid enum values).
			// Falls through to default/normal handling for now.
			fallthrough
		case SIGNAL_NORMAL:
			// No special handling needed beyond initial generation/mutation.
			fallthrough
		default:
			// No special handling for unknown types or types falling through.
		}
	}
}

func (s *SmartStrategy) GenerateTestCase(iteration int) map[string]string {
	r := rand.New(rand.NewSource(s.seed + int64(iteration)))

	testCase := make(map[string]string)

	if s.module == nil {
		log.Println("Warning: SmartStrategy module not set, returning empty test case.")
		return testCase
	}

	// Decide whether to mutate a previous run or generate a new one
	shouldMutate := len(s.previousRuns) > 5 &&
		r.Intn(4) == 0 // 25% chance to mutate if enough history

	if shouldMutate {
		// Select a random previous run as the base
		baseCaseIndex := r.Intn(len(s.previousRuns))
		baseCase := s.previousRuns[baseCaseIndex]
		testCase = s.mutateTestCase(baseCase, r)
	} else {
		// Generate a completely new test case using smart strategies
		testCase = s.generateNewTestCase(r)
	}

	// Apply constraints and special signal handling to the generated/mutated case
	s.applyConstraints(testCase, r)

	// Store this test case for future mutation
	// Limit the size of previousRuns history
	if len(s.previousRuns) >= 20 {
		// Remove the oldest run
		s.previousRuns = s.previousRuns[1:]
	}
	// Add the new run
	// Make a copy to avoid modification issues if map is reused elsewhere
	finalTestCase := make(map[string]string)
	for k, v := range testCase {
		finalTestCase[k] = v
	}
	s.previousRuns = append(s.previousRuns, finalTestCase)

	return finalTestCase // Return the potentially constrained test case
}
