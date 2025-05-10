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
	if width <= 0 {
		return "0"
	}

	hexDigits := (width + 3) / 4
	if hexDigits == 0 {
		hexDigits = 1
	}

	if width == 1 {
		return strconv.Itoa(r.Intn(2))
	}

	var value uint64
	effectiveWidth := width
	if effectiveWidth > 64 {
		effectiveWidth = 64
	}

	mask := uint64(0)
	if effectiveWidth > 0 {
		if effectiveWidth == 64 {
			mask = 0xFFFFFFFFFFFFFFFF
		} else {
			mask = (uint64(1) << effectiveWidth) - 1
		}
	}

	numStrategies := 6 // Base: all_zeros, all_ones, single_bit, small_num, near_max, alternating
	if width == 32 {
		numStrategies = 7 // Add special 32-bit patterns
	} else if width < 4 {
		numStrategies = 4 // Fewer for very narrow: all_zeros, all_ones, single_bit, random (covered by small_num/default)
	}

	strategy := r.Intn(numStrategies)

	switch strategy {
	case 0: // All zeros
		value = 0
	case 1: // All ones
		value = mask
	case 2: // Single bit set
		bitPos := r.Intn(width)
		if bitPos < 64 {
			value = uint64(1) << bitPos
		} else {
			value = uint64(1) << (r.Intn(64))
		}
	case 3: // Small number (0-255 or up to mask)
		smallRangeMax := uint64(255)
		if effectiveWidth > 0 && mask < smallRangeMax {
			smallRangeMax = mask
		} else if effectiveWidth == 0 {
			smallRangeMax = 0
		}

		if smallRangeMax == 0xFFFFFFFFFFFFFFFF {
			value = r.Uint64()
		} else if smallRangeMax > 0 {
			value = r.Uint64() % (smallRangeMax + 1)
		} else {
			value = 0
		}
	case 4: // Number near max value
		if mask > 10 {
			offset := r.Uint64() % 10
			if mask >= offset {
				value = mask - offset
			} else {
				value = mask
			}
		} else {
			value = r.Uint64() // Or simply `value = mask`
		}
	case 5: // Alternating bits
		if r.Intn(2) == 0 {
			value = 0x5555555555555555
		} else {
			value = 0xAAAAAAAAAAAAAAAA
		}
	case 6: // Special 32-bit patterns (only if width == 32)
		if width == 32 {
			patterns := []uint64{
				0xdeadbeef,
				0xcafebabe,
				0xa5a5a5a5,
				0x01234567,
				0xfedcba98,
				0x00004000,
				0x80000000,
				0x55555555,
				0xaaaaaaaa,
			}
			value = patterns[r.Intn(len(patterns))]
		} else {
			value = r.Uint64()
		}
	default: // Fully random
		value = r.Uint64()
	}

	value &= mask
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
			hexDigits := (port.Width + 3) / 4 // Calculate hex digits needed
			if hexDigits == 0 {
				hexDigits = 1 // Ensure at least one digit
			}

			if port.Width == 1 {
				// For single-bit ports
				testCase[port.Name] = strconv.Itoa(r.Intn(2))
			} else {
				// For multi-bit ports, use different strategies
				strategy := r.Intn(5)
				switch strategy {
				case 0: // All zeros
					testCase[port.Name] = strings.Repeat("0", hexDigits) // Use padded zeros
				case 1: // All ones - with proper width
					testCase[port.Name] = strings.Repeat("f", hexDigits)
				case 2: // Single bit set
					bitPos := r.Intn(port.Width)
					value := uint64(1) << bitPos
					testCase[port.Name] = fmt.Sprintf("%0*x", hexDigits, value)
				case 3: // Alternating bits
					pattern := uint64(0)
					for i := 0; i < port.Width && i < 64; i += 2 {
						pattern |= (uint64(1) << i)
					}
					testCase[port.Name] = fmt.Sprintf("%0*x", hexDigits, pattern)
				default: // Random value with proper width
					testCase[port.Name] = GenerateHexValue(port.Width, r) // This function already handles padding
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

// generateDataPortValue generates a value for a data port using various strategies,
// now aware of port.Type from parser.go and properly respects port.Width
func (s *SmartStrategy) generateDataPortValue( //nolint:gocyclo
	port verilog.Port,
	r *rand.Rand,
) string {
	// First determine the value distribution strategy (small, middle, large, random)
	distributionChoice := r.Intn(5)
	valuePreference := ""

	switch distributionChoice {
	case 0:
		valuePreference = "min" // Prefer minimal/smallest values
	case 1:
		valuePreference = "max" // Prefer maximal/largest values
	case 2:
		valuePreference = "mid" // Prefer middle-range values
	case 3:
		valuePreference = "extreme" // Prefer extremes (min or max)
	default:
		valuePreference = "random" // Fully random - use existing distribution
	}

	// Ensure we have a valid width, defaulting to type-specific width if port.Width is zero
	width := port.Width
	if width <= 0 {
		width = verilog.GetWidthForType(port.Type)
		// If still zero (unknown type), default to 1
		if width <= 0 {
			width = 1
		}
	}

	// Handle specific Verilog types that don't map well to simple hex values
	switch port.Type {
	case verilog.REAL, verilog.REALTIME, verilog.SHORTREAL:
		var fVal float64

		switch valuePreference {
		case "min":
			if r.Intn(5) == 0 { // Occasionally extreme min
				return "-1.0e38" // Very large negative
			}
			// Small negative values
			fVal = -r.Float64() * 10.0
		case "max":
			if r.Intn(5) == 0 { // Occasionally extreme max
				return "1.0e38" // Very large positive
			}
			// Large positive values
			fVal = r.Float64() * 1000.0
		case "mid":
			// Values around zero
			fVal = (r.Float64() - 0.5) * 10.0
		case "extreme":
			if r.Intn(2) == 0 {
				return "-1.0e38" // Extreme negative
			} else {
				return "1.0e38" // Extreme positive
			}
		default: // random - use existing distribution
			strat := r.Intn(5)
			switch strat {
			case 0:
				fVal = 0.0
			case 1:
				fVal = (r.Float64() - 0.5) * 2.0 // Small value around 0
			case 2:
				fVal = (r.Float64() - 0.5) * 2.0e10 // Large value
				if r.Intn(4) == 0 {                 // Occasionally very large/small
					fVal *= r.Float64() * 1e20
				}
			case 3:
				fVal = r.NormFloat64() * 1000 // Gaussian distribution
			case 4:
				fVal = float64(r.Intn(2000) - 1000) // Integer-like floats
			}
		}

		// Add extremal IEEE 754 values sometimes
		if r.Intn(20) == 0 { // Inf, -Inf, NaN
			switch r.Intn(3) {
			case 0:
				return "1.0/0.0" // Positive Infinity for Verilog
			case 1:
				return "-1.0/0.0" // Negative Infinity for Verilog
			case 2:
				return "0.0/0.0" // NaN for Verilog
			}
		}
		return fmt.Sprintf("%g", fVal)

	case verilog.STRING:
		strat := r.Intn(5)
		var strVal string
		chars := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_ " // Space included

		// Adjust string generation based on value preference
		switch valuePreference {
		case "min":
			if r.Intn(3) == 0 {
				strVal = "" // Empty string - smallest possible
			} else {
				// Very short string
				length := r.Intn(3) + 1
				b := make([]byte, length)
				for i := range b {
					b[i] = chars[r.Intn(len(chars))]
				}
				strVal = string(b)
			}
		case "max":
			// Very long string
			length := r.Intn(200) + 100
			b := make([]byte, length)
			for i := range b {
				b[i] = chars[r.Intn(len(chars))]
			}
			strVal = string(b)
		case "mid":
			// Medium length string
			length := r.Intn(20) + 10
			b := make([]byte, length)
			for i := range b {
				b[i] = chars[r.Intn(len(chars))]
			}
			strVal = string(b)
		case "extreme":
			if r.Intn(2) == 0 {
				strVal = "" // Empty string
			} else {
				// Very long string
				length := r.Intn(200) + 150
				b := make([]byte, length)
				for i := range b {
					b[i] = chars[r.Intn(len(chars))]
				}
				strVal = string(b)
			}
		default: // Use existing distribution
			switch strat {
			case 0: // Empty string
				strVal = ""
			case 1: // Short random alphanumeric string
				length := r.Intn(10) + 1 // 1-10 chars
				b := make([]byte, length)
				for i := range b {
					b[i] = chars[r.Intn(len(chars))]
				}
				strVal = string(b)
			case 2: // Longer random alphanumeric string
				length := r.Intn(50) + 10 // 10-59 chars
				if r.Intn(10) == 0 {      // Occasionally very long
					length = r.Intn(200) + 50 // 50-249
				}
				b := make([]byte, length)
				for i := range b {
					b[i] = chars[r.Intn(len(chars))]
				}
				strVal = string(b)
			case 3: // String with some common punctuation
				punctuations := "!@#$%^&*()_+-=[]{}|;':,.<>?/" // Avoid backslash and double quote for simplicity here
				length := r.Intn(10) + 5
				b := make([]byte, length)
				for i := range b {
					if r.Intn(4) == 0 {
						b[i] = punctuations[r.Intn(len(punctuations))]
					} else {
						b[i] = chars[r.Intn(len(chars))]
					}
				}
				strVal = string(b)
			case 4: // Numeric string
				strVal = strconv.FormatInt(r.Int63n(1000000)-500000, 10) // numbers pos/neg
			}
		}
		return fmt.Sprintf("\"%s\"", strings.ReplaceAll(strVal, "\"", "\\\""))

	case verilog.TIME:
		var timeVal int64
		units := []string{"fs", "ps", "ns", "us", "ms", "s"}
		unit := units[r.Intn(len(units))]

		switch valuePreference {
		case "min":
			if r.Intn(3) == 0 {
				return "\"0ps\"" // Zero time - minimum
			}
			timeVal = r.Int63n(10) + 1 // Very small (1-10)
		case "max":
			if r.Intn(3) == 0 {
				return fmt.Sprintf("\"%d%s\"", 0x7FFFFFFF, unit) // Very large
			}
			timeVal = r.Int63n(10000000) + 9000000 // Near max (9M-19M)
		case "mid":
			timeVal = r.Int63n(5000) + 2500 // Middle range (2500-7499)
		case "extreme":
			if r.Intn(2) == 0 {
				return "\"0ps\"" // Minimum
			} else {
				return fmt.Sprintf("\"%d%s\"", 0x7FFFFFFF, unit) // Maximum
			}
		default: // Use existing distribution
			strat := r.Intn(4)
			switch strat {
			case 0: // Zero time
				return "\"0ps\"" // Explicit zero time with a unit
			case 1: // Small time value
				timeVal = r.Int63n(100) + 1 // 1-100
			case 2: // Medium time value
				timeVal = r.Int63n(10000) + 1 // 1-10000
			case 3: // Large time value
				timeVal = r.Int63n(10000000) + 1 // 1-10,000,000
			}
		}
		return fmt.Sprintf("\"%d%s\"", timeVal, unit)

	case verilog.INTEGER, verilog.INT:
		// Handle signed integer values based on specified width
		var value int64

		// Calculate maximum positive and negative values based on width
		maxPositive := int64((uint64(1) << (width - 1)) - 1) // 2^(width-1) - 1
		minNegative := -int64(uint64(1) << (width - 1))      // -2^(width-1)

		// Ensure we don't exceed int32/int64 boundaries
		if width > 32 {
			if maxPositive > 0x7FFFFFFFFFFFFFFF {
				maxPositive = 0x7FFFFFFFFFFFFFFF
			}
			if minNegative < -0x7FFFFFFFFFFFFFFF {
				minNegative = -0x7FFFFFFFFFFFFFFF
			}
		}

		switch valuePreference {
		case "min":
			if r.Intn(4) == 0 {
				value = minNegative // Minimum int32
			} else {
				value = -int64(r.Intn(1000) + 1) // Small negative (-1001 to -1)
			}
		case "max":
			if r.Intn(4) == 0 {
				value = maxPositive // Maximum int32
			} else {
				// Large positive but below max
				offset := int64(r.Intn(100))
				if maxPositive > offset {
					value = maxPositive - offset
				} else {
					value = maxPositive
				}
			}
		case "mid":
			// Values around zero or middle of range based on width
			if width <= 8 {
				// For small widths, use scaled values
				midPoint := int64(r.Intn(width*2) - width)
				value = midPoint
			} else {
				midPoint := int64(r.Intn(10000) - 5000) // Values around zero (-5000 to 4999)

				// Ensure we're within range for the width
				if midPoint > maxPositive {
					midPoint = maxPositive
				}
				if midPoint < minNegative {
					midPoint = minNegative
				}
				value = midPoint
			}
		case "extreme":
			if r.Intn(2) == 0 {
				value = minNegative // Minimum for width
			} else {
				value = maxPositive // Maximum for width
			}
		default: // Use existing distribution with width awareness
			strat := r.Intn(10)
			switch strat {
			case 0: // Zero
				value = 0
			case 1: // Max positive for width
				value = maxPositive
			case 2: // Max negative for width
				value = minNegative
			case 3: // Near max positive
				if maxPositive > 100 {
					offset := int64(r.Intn(100))
					value = maxPositive - offset
				} else {
					value = maxPositive // Just use max if it's small
				}
			case 4: // Near max negative
				if minNegative < -100 {
					offset := int64(r.Intn(100))
					value = minNegative + offset
				} else {
					value = minNegative // Just use min if it's small
				}
			case 5: // Small positive
				value = int64(r.Intn(100) + 1)
			case 6: // Small negative
				value = -int64(r.Intn(100) + 1)
			case 7: // Powers of 2 (positive)
				// Ensure power is within the width limit
				maxExp := width - 2 // -2 for signed (need 1 sign bit, and stay under max)
				if maxExp < 0 {
					maxExp = 0
				}
				exp := r.Intn(maxExp + 1)
				value = int64(1) << exp
			case 8: // Powers of 2 (negative)
				// Ensure power is within the width limit
				maxExp := width - 2 // -2 for signed (need 1 sign bit, and stay under max)
				if maxExp < 0 {
					maxExp = 0
				}
				exp := r.Intn(maxExp + 1)
				value = -int64(1) << exp
			case 9: // Fully random within width range
				// Generate a random value within the range for the width
				range64 := maxPositive - minNegative + 1
				if range64 > 0 && range64 < 1000000 { // Avoid massive ranges that could overflow
					randomOffset := int64(r.Uint64() % uint64(range64))
					value = minNegative + randomOffset
				} else {
					// For extremely large widths, fall back to simpler approach
					value = int64(r.Int63())
					if r.Intn(2) == 0 { // 50% chance of negative
						value = -value
					}
				}
			}
		}

		// Format based on width - use hex for wider values for readability
		if width > 16 {
			return fmt.Sprintf("0x%x", value)
		}
		return fmt.Sprintf("%d", value)

	case verilog.BIT:
		// BIT is always 0 or 1 for single bit, otherwise treat like LOGIC
		if width == 1 {
			if valuePreference == "min" {
				return "0" // Minimal value is 0
			} else if valuePreference == "max" {
				return "1" // Maximal value is 1
			} else {
				return strconv.Itoa(r.Intn(2)) // Random 0/1
			}
		}
		// For multi-bit BIT vectors, use the same approach as LOGIC
		fallthrough

	case verilog.LOGIC, verilog.REG, verilog.WIRE:
		// For LOGIC, WIRE, REG types, handle specifically based on width
		if width == 1 {
			if valuePreference == "min" {
				return "0" // Minimal value is 0
			} else if valuePreference == "max" {
				return "1" // Maximal value is 1
			} else {
				return strconv.Itoa(r.Intn(2)) // Random 0/1
			}
		}

		// For multi-bit values, calculate proper hex digits for specified width
		hexDigits := (width + 3) / 4
		if hexDigits == 0 {
			hexDigits = 1
		}

		var value uint64
		effectiveWidth := width
		if effectiveWidth > 64 {
			effectiveWidth = 64
		}

		// Calculate mask for the actual port width
		mask := uint64(0)
		if effectiveWidth > 0 {
			if effectiveWidth == 64 {
				mask = 0xFFFFFFFFFFFFFFFF
			} else {
				mask = (uint64(1) << effectiveWidth) - 1
			}
		}

		switch valuePreference {
		case "min":
			value = 0 // All zeros for minimum
		case "max":
			value = mask // All ones for maximum
		case "mid":
			// Middle value - set approximately half the bits based on actual width
			if effectiveWidth < 64 {
				midWidth := effectiveWidth / 2
				if midWidth > 0 {
					midValue := uint64(1) << midWidth
					if midValue > 0 {
						value = midValue - 1 // e.g., 0x007F for 8-bit
					}
				}
			} else {
				value = 0x00000000FFFFFFFF // Middle value for 64-bit
			}
		case "extreme":
			if r.Intn(2) == 0 {
				value = 0 // Minimum
			} else {
				value = mask // Maximum
			}
		default: // Use existing distribution - more variety
			strat := r.Intn(8)
			switch strat {
			case 0: // All zeros
				value = 0
			case 1: // All ones within width
				value = mask
			case 2: // Alternating 01010... (respecting width)
				value = 0x5555555555555555 & mask
			case 3: // Alternating 10101... (respecting width)
				value = 0xAAAAAAAAAAAAAAAA & mask
			case 4: // Single bit set (random position within width)
				bitPos := 0
				if width > 0 {
					bitPos = r.Intn(width)
				}
				if bitPos < 64 {
					value = uint64(1) << bitPos
				} else {
					value = uint64(1) << (r.Intn(64))
				}
			case 5: // Value near maximum (respecting width)
				offset := r.Uint64() % 16
				if mask >= offset {
					value = mask - offset
				} else {
					value = mask
				}
			case 6: // Value near minimum (small positive)
				value = r.Uint64() % 16
			default: // Random value within width range
				value = r.Uint64() & mask
			}
		}

		return fmt.Sprintf("%0*x", hexDigits, value)

	case verilog.BYTE:
		// BYTE is 8-bit unsigned integer
		var value uint8

		switch valuePreference {
		case "min":
			if r.Intn(4) == 0 {
				value = 0 // Absolute minimum
			} else {
				value = uint8(r.Intn(5) + 1) // Small values (1-5)
			}
		case "max":
			if r.Intn(4) == 0 {
				value = 0xFF // Absolute maximum (255)
			} else {
				value = uint8(0xFF - r.Intn(5)) // Near max (251-254)
			}
		case "mid":
			value = uint8(0x7F + r.Intn(17) - 8) // Middle range (119-135)
		case "extreme":
			if r.Intn(2) == 0 {
				value = 0x00 // Minimum
			} else {
				value = 0xFF // Maximum
			}
		default: // Use existing distribution
			strat := r.Intn(10)
			switch strat {
			case 0: // Zero
				value = 0
			case 1: // Max value
				value = 0xFF // 255
			case 2: // One
				value = 1
			case 3: // Middle value
				value = 0x80 // 128
			case 4: // Half-middle low
				value = 0x40 // 64
			case 5: // Half-middle high
				value = 0xC0 // 192
			case 6: // ASCII printable range
				value = uint8(r.Intn(95) + 32) // 32-126 ASCII
			case 7: // One less than max
				value = 0xFE // 254
			case 8: // Powers of 2
				exp := r.Intn(8) // 0-7 for 2^0 to 2^7
				value = 1 << exp
			default: // Fully random
				value = uint8(r.Intn(256))
			}
		}

		// Format as 2-digit hex value
		return fmt.Sprintf("%02x", value)

	case verilog.SHORTINT:
		// SHORTINT is 16-bit signed integer
		var value int16

		switch valuePreference {
		case "min":
			if r.Intn(4) == 0 {
				value = -0x8000 // Minimum int16 (-32768)
			} else {
				value = int16(-r.Intn(100) - 1) // Small negative (-101 to -1)
			}
		case "max":
			if r.Intn(4) == 0 {
				value = 0x7FFF // Maximum int16 (32767)
			} else {
				value = int16(0x7FFF - r.Intn(100)) // Near max (32667-32766)
			}
		case "mid":
			value = int16(r.Intn(1000) - 500) // Middle range (-500 to 499)
		case "extreme":
			if r.Intn(2) == 0 {
				value = -0x8000 // Minimum
			} else {
				value = 0x7FFF // Maximum
			}
		default: // Use existing distribution
			strat := r.Intn(10)
			switch strat {
			case 0: // Zero
				value = 0
			case 1: // Extremal: Max positive
				value = 0x7FFF // 32767
			case 2: // Extremal: Max negative
				value = -0x8000 // -32768
			case 3: // Near max positive
				value = 0x7FFF - int16(r.Intn(100))
			case 4: // Near max negative
				value = -0x8000 + int16(r.Intn(100))
			case 5: // Small positive
				value = int16(r.Intn(100) + 1)
			case 6: // Small negative
				value = int16(-r.Intn(100) - 1)
			case 7: // Powers of 2 (positive)
				exp := r.Intn(15) // 0-14 to stay within int16 range
				value = 1 << exp
			case 8: // Powers of 2 (negative)
				exp := r.Intn(15) // 0-14 to stay within int16 range
				if exp < 15 {     // Avoid overflow
					value = -1 * (1 << exp)
				} else {
					value = -0x4000 // Use -2^14 as safer alternative
				}
			case 9: // Fully random
				value = int16(r.Intn(65536) - 32768) // Full int16 range
			}
		}

		// Format as signed decimal value
		return fmt.Sprintf("%d", value)

	case verilog.LONGINT:
		// LONGINT is 64-bit signed integer
		var value int64

		switch valuePreference {
		case "min":
			if r.Intn(4) == 0 {
				value = -0x7FFFFFFFFFFFFFFF - 1 // Minimum int64
			} else {
				value = -r.Int63n(10000) - 1 // Small negative (-10001 to -1)
			}
		case "max":
			if r.Intn(4) == 0 {
				value = 0x7FFFFFFFFFFFFFFF // Maximum int64
			} else {
				value = r.Int63n(10000) + (0x7FFFFFFFFFFFFFFF - 10000) // Near max
			}
		case "mid":
			value = r.Int63n(20000) - 10000 // Middle range (-10000 to 9999)
		case "extreme":
			if r.Intn(2) == 0 {
				value = -0x7FFFFFFFFFFFFFFF - 1 // Minimum
			} else {
				value = 0x7FFFFFFFFFFFFFFF // Maximum
			}
		default: // Use existing distribution
			strat := r.Intn(10)
			switch strat {
			case 0: // Zero
				value = 0
			case 1: // Extremal: Large positive (not quite max to avoid overflow issues)
				value = 0x7FFFFFFFFFFFFFFF - r.Int63n(1000)
			case 2: // Extremal: Large negative
				value = -0x7FFFFFFFFFFFFFFF + r.Int63n(1000)
			case 3: // Small positive
				value = r.Int63n(1000) + 1
			case 4: // Small negative
				value = -r.Int63n(1000) - 1
			case 5: // Powers of 2 (positive)
				exp := r.Intn(63) // 0-62 to stay within int64 range
				value = 1 << exp
			case 6: // Powers of 2 (negative)
				exp := r.Intn(63) // 0-62 to stay within int64 range
				value = -1 * (1 << exp)
			case 7: // Medium range positive
				value = r.Int63n(1000000) + 1000
			case 8: // Medium range negative
				value = -r.Int63n(1000000) - 1000
			case 9: // Fully random
				value = r.Int63()
				if r.Intn(2) == 0 { // 50% chance of negative
					value = -value
				}
			}
		}

		// Format as signed decimal value or hex for very large values
		if value > 1000000000 || value < -1000000000 {
			// Use hex for very large values to avoid potential formatting issues
			return fmt.Sprintf("0x%x", value)
		}
		return fmt.Sprintf("%d", value)
	}

	// Default to hex generation for bit-vector types (REG, WIRE, etc.)
	if width <= 0 {
		return "0"
	}

	hexDigits := (width + 3) / 4
	if hexDigits == 0 {
		hexDigits = 1
	}

	if width == 1 {
		// Respect value preference for single-bit values
		switch valuePreference {
		case "min":
			return "0"
		case "max":
			return "1"
		default:
			return strconv.Itoa(r.Intn(2))
		}
	}

	var value uint64
	var generatedHex string

	effectiveWidth := width
	if effectiveWidth > 64 {
		effectiveWidth = 64
	}

	// Calculate mask based on ACTUAL width to ensure values are in range
	mask := uint64(0)
	if effectiveWidth > 0 {
		if effectiveWidth == 64 {
			mask = 0xFFFFFFFFFFFFFFFF
		} else {
			mask = (uint64(1) << effectiveWidth) - 1
		}
	}

	// Use valuePreference to guide value generation for generic bit vectors
	switch valuePreference {
	case "min":
		if r.Intn(5) == 0 {
			value = 0 // Absolute minimum (all zeros)
		} else {
			value = r.Uint64() % 10 // Very small value (0-9)
		}
	case "max":
		if r.Intn(5) == 0 {
			value = mask // Absolute maximum (all ones for this width)
		} else {
			// Very close to max for this width
			value = mask - (r.Uint64() % 10)
		}
	case "mid":
		// Mid-range - set approximately half the bits based on actual port width
		if effectiveWidth > 1 {
			halfWidth := effectiveWidth / 2
			if halfWidth < 64 {
				halfMask := (uint64(1) << halfWidth) - 1
				value = halfMask
			} else {
				value = 0xFFFFFFFF // Half of 64-bit
			}

			// Add some randomness around the middle value
			if r.Intn(2) == 0 {
				offset := r.Uint64() % 100
				if value >= offset {
					value = value - offset // Slightly below middle
				}
			} else {
				value = value + (r.Uint64() % 100) // Slightly above middle
				if value > mask {
					value = mask // Cap at maximum for this width
				}
			}
		} else {
			// For width=1, mid is arbitrary (0 or 1)
			value = uint64(r.Intn(2))
		}
	case "extreme":
		if r.Intn(2) == 0 {
			value = 0 // Minimum
		} else {
			value = mask // Maximum for this width
		}
	default: // random - use existing strategies with width awareness
		numHexStrategies := 10
		strategy := r.Intn(numHexStrategies)

		switch strategy {
		case 0: // All zeros
			value = 0
		case 1: // All ones (for this width)
			value = mask
		case 2: // Single bit set within width
			bitPos := 0
			if width > 0 {
				bitPos = r.Intn(width)
			}

			if bitPos < 64 {
				value = uint64(1) << bitPos
			} else {
				value = uint64(1) << (r.Intn(64))
			}
			value &= mask
		case 3: // Alternating bits (0101...) - limited to width
			value = 0x5555555555555555 & mask
		case 4: // Alternating bits (1010...) - limited to width
			value = 0xAAAAAAAAAAAAAAAA & mask
		case 5: // Small integer (0-255), represented as hex
			smallVal := r.Uint64() % 256
			value = smallVal & mask
		case 6: // Powers of 2 within width limit
			// Ensure power doesn't exceed width
			maxPower := width - 1
			if maxPower < 0 {
				maxPower = 0
			}

			power := 0
			if maxPower > 0 {
				power = r.Intn(maxPower + 1)
			}

			if power < 64 {
				value = uint64(1) << power
			} else {
				value = uint64(1) << (r.Intn(64))
			}
			value &= mask
		case 7: // Powers of 2 minus 1 (limited by width)
			limit := width
			if limit <= 0 {
				limit = 1
			}

			// Ensure power is at least 1 for (1<<power)-1 to be meaningful
			power := 1
			if limit > 1 {
				power = r.Intn(limit-1) + 1
				// Don't exceed port width
				if power > width {
					power = width
				}
			}

			if power >= 64 {
				value = 0xFFFFFFFFFFFFFFFF
			} else {
				value = (uint64(1) << power) - 1
			}
			value &= mask
		case 8: // Value near maximum for the specific port width
			offset := r.Uint64() % 16 // Small offset 0-15
			if mask >= offset {
				value = mask - offset
			} else {
				value = mask
			}
		default: // Fully random value using the enhanced GenerateHexValue
			// This allows GenerateHexValue's internal strategies to be used with the correct width
			generatedHex = GenerateHexValue(width, r)
			return generatedHex
		}
	}

	// Format with the correct number of hex digits for this width
	generatedHex = fmt.Sprintf("%0*x", hexDigits, value)
	return generatedHex
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
