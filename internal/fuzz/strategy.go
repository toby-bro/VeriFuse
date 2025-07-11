package fuzz

import (
	"fmt"
	"math"
	"math/rand"
	"strconv"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/verilog"
)

type Strategy interface {
	GenerateTestCase(iteration int) map[*verilog.Port]string
	SetModule(module *verilog.Module)
	Name() string
}

type RandomStrategy struct {
	module *verilog.Module
}

func NewRandomInputStrategy() *RandomStrategy {
	return &RandomStrategy{}
}

func (s *RandomStrategy) SetModule(module *verilog.Module) {
	s.module = module
}

func (s *RandomStrategy) Name() string {
	return "RandomStrategy"
}

func (s *RandomStrategy) GenerateTestCase(_ int) map[*verilog.Port]string {
	if s.module == nil {
		return make(map[*verilog.Port]string)
	}

	inputs := make(map[*verilog.Port]string)
	for _, port := range s.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			inputs[port] = generateRandomValue(port.Type, port.Width, port.IsSigned)
		}
	}
	return inputs
}

// Helper to generate a random hex string for a given bit width
func randomHex(width int) string {
	if width <= 0 {
		return "0" // Return "0" for non-positive widths
	}
	numHexChars := (width + 3) / 4
	var sb strings.Builder
	for i := 0; i < numHexChars; i++ {
		nibble := rand.Intn(16)
		if i == 0 && width%4 != 0 { // Mask the first nibble if width is not a multiple of 4
			mask := (1 << (width % 4)) - 1
			nibble &= mask
		}
		sb.WriteString(fmt.Sprintf("%x", nibble))
	}
	return sb.String()
}

// Helper to generate max hex string (all 1s) for a given bit width
func maxHex(width int) string {
	if width <= 0 {
		return "0"
	}
	numHexChars := (width + 3) / 4
	var sb strings.Builder

	// Handle the first nibble if width is not a multiple of 4
	if width%4 != 0 {
		mask := (1 << (width % 4)) - 1
		sb.WriteString(fmt.Sprintf("%x", mask))
	}

	// Fill remaining full nibbles with 'f'
	startNibble := 0
	if width%4 != 0 {
		startNibble = 1
	}
	for i := startNibble; i < numHexChars; i++ {
		sb.WriteString("f")
	}

	// If the width was a multiple of 4, the above loop for width%4!=0 didn't run.
	// Fill all nibbles with 'f' in that case.
	if width%4 == 0 {
		sb.Reset() // Clear anything that might have been added (should be empty)
		for i := 0; i < numHexChars; i++ {
			sb.WriteString("f")
		}
	}

	if sb.Len() == 0 { // Should only happen if width was 0, handled at the start
		return "0"
	}

	return sb.String()
}

func generateRandomValue(portType verilog.PortType, width int, isSigned bool) string {
	switch portType {
	case verilog.REG, verilog.WIRE, verilog.LOGIC, verilog.BIT:
		effectiveWidth := width
		if effectiveWidth <= 0 {
			effectiveWidth = 1
		}
		return randomHex(effectiveWidth)

	case verilog.INTEGER: // Verilog integer: 32-bit signed
		var val int32
		val = rand.Int31()
		if rand.Intn(2) == 1 {
			val = -val
		}
		return strconv.FormatUint(uint64(uint32(val)), 16) // Cast to uint32

	case verilog.INT: // SystemVerilog int: 32-bit signed
		var val int32
		val = rand.Int31()
		if rand.Intn(2) == 1 {
			val = -val
		}
		return strconv.FormatUint(uint64(uint32(val)), 16) // Cast to uint32

	case verilog.BYTE: // 8-bit
		if isSigned {
			// Generate a random int8 value, then cast to uint8 for hex representation
			randBits := rand.Intn(1 << 8)
			val := int8(randBits)
			return strconv.FormatUint(uint64(uint8(val)), 16)
		}
		return strconv.FormatUint(uint64(uint8(rand.Intn(1<<8))), 16)

	case verilog.SHORTINT: // 16-bit
		if isSigned {
			randBits := rand.Intn(1 << 16)
			val := int16(randBits)
			return strconv.FormatUint(uint64(uint16(val)), 16)
		}
		return strconv.FormatUint(uint64(uint16(rand.Intn(1<<16))), 16)

	case verilog.LONGINT: // 64-bit
		if isSigned {
			val := int64(rand.Uint64()) // Full range for int64
			return strconv.FormatUint(uint64(val), 16)
		}
		return strconv.FormatUint(rand.Uint64(), 16)

	case verilog.TIME: // 64-bit unsigned
		return strconv.FormatUint(rand.Uint64(), 16)

	// Floating point and string types remain unchanged as they are not typically represented as raw hex numbers in this context.
	case verilog.REAL, verilog.REALTIME:
		return strconv.FormatFloat(rand.Float64(), 'g', -1, 64)

	case verilog.SHORTREAL:
		return strconv.FormatFloat(float64(rand.Float32()), 'g', -1, 32)

	case verilog.STRING:
		length := 5 + rand.Intn(16)
		charSet := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_ "
		runes := make([]rune, length)
		for i := range runes {
			runes[i] = rune(charSet[rand.Intn(len(charSet))])
		}
		return "\\\"" + string(runes) + "\\\""

	case verilog.ENUM, verilog.STRUCT, verilog.USERDEFINED, verilog.VOID, verilog.UNKNOWN:
		effectiveWidth := width
		if effectiveWidth <= 0 {
			effectiveWidth = 1
		}
		numHexChars := (effectiveWidth + 3) / 4
		if numHexChars <= 0 {
			numHexChars = 1
		}
		return strings.Repeat("x", numHexChars)

	case verilog.TYPE:
		return ""

	case verilog.INTERFACE:
		// Interface ports are complex and require special handling
		// They contain multiple signals and should not be treated as simple hex values
		return "INTERFACE_PORT"

	default:
		return "x"
	}
}

type SmartStrategy struct {
	module *verilog.Module
}

func NewSmartStrategy() *SmartStrategy {
	return &SmartStrategy{}
}

func (s *SmartStrategy) SetModule(module *verilog.Module) {
	s.module = module
}

func (s *SmartStrategy) Name() string {
	return "SmartStrategy"
}

func (s *SmartStrategy) GenerateTestCase(_ int) map[*verilog.Port]string {
	if s.module == nil {
		return make(map[*verilog.Port]string)
	}

	inputs := make(map[*verilog.Port]string)
	for _, port := range s.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			inputs[port] = generateSmartValue(port.Type, port.Width, port.IsSigned)
		}
	}
	return inputs
}

func generateSmartValue(portType verilog.PortType, width int, isSigned bool) string {
	if rand.Intn(2) == 0 { // 50% chance for edge case
		return generateEdgeCaseValue(portType, width, isSigned)
	}
	return generateRandomValue(portType, width, isSigned) // 50% chance for random
}

func generateEdgeCaseValue( // nolint:gocyclo
	portType verilog.PortType,
	width int,
	isSigned bool,
) string {
	pickMin := rand.Intn(2) == 0 // 50% chance to pick min, else max

	switch portType {
	case verilog.REG, verilog.WIRE, verilog.LOGIC, verilog.BIT:
		effectiveWidth := width
		if effectiveWidth <= 0 {
			effectiveWidth = 1
		}
		if pickMin {
			return "0"
		}
		return maxHex(effectiveWidth)

	case verilog.INTEGER, verilog.INT: // 32-bit signed
		if pickMin {
			minInt32Val := int32(math.MinInt32)
			return strconv.FormatUint(uint64(uint32(minInt32Val)), 16)
		}
		maxInt32Val := int32(math.MaxInt32)
		return strconv.FormatUint(uint64(uint32(maxInt32Val)), 16)

	case verilog.BYTE: // 8-bit
		if isSigned {
			if pickMin {
				val := int8(math.MinInt8)
				return strconv.FormatUint(uint64(uint8(val)), 16)
			}
			val := int8(math.MaxInt8)
			return strconv.FormatUint(uint64(uint8(val)), 16)
		}
		// Unsigned
		if pickMin {
			return "0"
		}
		return strconv.FormatUint(uint64(uint8(math.MaxUint8)), 16)

	case verilog.SHORTINT: // 16-bit
		if isSigned {
			if pickMin {
				val := int16(math.MinInt16)
				return strconv.FormatUint(uint64(uint16(val)), 16)
			}
			val := int16(math.MaxInt16)
			return strconv.FormatUint(uint64(uint16(val)), 16)
		}
		// Unsigned
		if pickMin {
			return "0"
		}
		return strconv.FormatUint(uint64(uint16(math.MaxUint16)), 16)

	case verilog.LONGINT: // 64-bit
		if isSigned {
			if pickMin {
				val := int64(math.MinInt64)
				return strconv.FormatUint(uint64(val), 16)
			}
			val := int64(math.MaxInt64)
			return strconv.FormatUint(uint64(val), 16)
		}
		// Unsigned
		if pickMin {
			return "0"
		}
		return strconv.FormatUint(uint64(math.MaxUint64), 16)

	case verilog.TIME: // 64-bit unsigned
		if pickMin {
			return "0"
		}
		return strconv.FormatUint(uint64(math.MaxUint64), 16)

	// Floating point and string types remain unchanged
	case verilog.REAL, verilog.REALTIME:
		if pickMin {
			if rand.Intn(2) == 0 {
				return "0.0"
			}
			return strconv.FormatFloat(-math.MaxFloat64, 'g', -1, 64)
		}
		return strconv.FormatFloat(math.MaxFloat64, 'g', -1, 64)

	case verilog.SHORTREAL:
		if pickMin {
			if rand.Intn(2) == 0 {
				return "0.0"
			}
			return strconv.FormatFloat(float64(-math.MaxFloat32), 'g', -1, 32)
		}
		return strconv.FormatFloat(float64(math.MaxFloat32), 'g', -1, 32)

	case verilog.STRING:
		if pickMin {
			return "\"\""
		}
		return "\"" + strings.Repeat("A", 20) + "\""

	case verilog.ENUM, verilog.STRUCT, verilog.USERDEFINED, verilog.VOID, verilog.UNKNOWN:
		effectiveWidth := width
		if effectiveWidth <= 0 {
			effectiveWidth = 1
		}
		numHexChars := (effectiveWidth + 3) / 4
		if numHexChars <= 0 {
			numHexChars = 1
		}
		return strings.Repeat("x", numHexChars)

	case verilog.TYPE:
		return ""

	case verilog.INTERFACE:
		// Interface ports are complex and require special handling
		// They contain multiple signals and should not be treated as simple hex values
		return "INTERFACE_PORT"

	default:
		return "x"
	}
}
