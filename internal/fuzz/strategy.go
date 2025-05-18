package fuzz

import (
	"math"
	"math/rand"
	"strconv"
	"strings"

	"github.com/toby-bro/pfuzz/internal/verilog"
)

type Strategy interface {
	GenerateTestCase(iteration int) map[string]string
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

func (s *RandomStrategy) GenerateTestCase(_ int) map[string]string {
	if s.module == nil {
		return make(map[string]string)
	}

	inputs := make(map[string]string)
	for _, port := range s.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			inputs[port.Name] = generateRandomValue(port.Type, port.Width, port.IsSigned)
		}
	}
	return inputs
}

func generateRandomValue(portType verilog.PortType, width int, isSigned bool) string {
	switch portType {
	case verilog.REG, verilog.WIRE, verilog.LOGIC, verilog.BIT:
		effectiveWidth := width
		if effectiveWidth <= 0 { // Treat 0 or negative width as 1 for scalar
			effectiveWidth = 1
		}

		if effectiveWidth == 1 {
			return strconv.Itoa(rand.Intn(2)) // "0" or "1"
		}

		var sb strings.Builder
		sb.WriteString(strconv.Itoa(effectiveWidth))
		sb.WriteString("'b")
		for i := 0; i < effectiveWidth; i++ {
			sb.WriteString(strconv.Itoa(rand.Intn(2)))
		}
		return sb.String()

	case verilog.INTEGER: // Verilog integer: 32-bit signed
		val := rand.Int31()
		if rand.Intn(2) == 1 { // 50% chance of being negative
			val = -val
		}
		return strconv.Itoa(int(val))

	case verilog.INT: // SystemVerilog int: 32-bit signed
		val := rand.Int31()
		if rand.Intn(2) == 1 { // 50% chance of being negative
			val = -val
		}
		return strconv.Itoa(int(val))

	case verilog.BYTE: // 8-bit
		if isSigned {
			return strconv.Itoa(int(int8(rand.Intn(1 << 8))))
		}
		return strconv.Itoa(rand.Intn(1 << 8)) // 0 to 255

	case verilog.SHORTINT: // 16-bit
		if isSigned {
			return strconv.Itoa(int(int16(rand.Intn(1 << 16))))
		}
		return strconv.Itoa(rand.Intn(1 << 16)) // 0 to 65535

	case verilog.LONGINT: // 64-bit
		if isSigned {
			return strconv.FormatInt(int64(rand.Uint64()), 10)
		}
		return strconv.FormatUint(rand.Uint64(), 10)

	case verilog.TIME: // 64-bit unsigned
		return strconv.FormatUint(rand.Uint64(), 10)

	case verilog.REAL, verilog.REALTIME: // double precision floating point
		return strconv.FormatFloat(rand.Float64(), 'g', -1, 64)

	case verilog.SHORTREAL: // single precision floating point
		return strconv.FormatFloat(float64(rand.Float32()), 'g', -1, 32)

	case verilog.STRING:

		length := 5 + rand.Intn(16)

		charSet := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_ "
		runes := make([]rune, length)
		for i := range runes {
			runes[i] = rune(charSet[rand.Intn(len(charSet))])
		}
		return "\"" + string(runes) + "\"" // Strings in Verilog are usually quoted

	case verilog.ENUM, verilog.STRUCT, verilog.USERDEFINED, verilog.VOID, verilog.UNKNOWN:

		effectiveWidth := width
		if effectiveWidth <= 0 {
			effectiveWidth = 1
		}
		if effectiveWidth > 1 {
			return strconv.Itoa(effectiveWidth) + "'bx" // e.g., 8'bx
		}
		return "'x" // For scalar unknown/complex types or void

	case verilog.TYPE: // Only for parameters
		return ""

	default:

		return "'x" // Default to 'x for safety
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

func (s *SmartStrategy) GenerateTestCase(_ int) map[string]string {
	if s.module == nil {
		return make(map[string]string)
	}

	inputs := make(map[string]string)
	for _, port := range s.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			inputs[port.Name] = generateSmartValue(port.Type, port.Width, port.IsSigned)
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
		if effectiveWidth == 1 {
			if pickMin {
				return "0"
			}
			return "1"
		}
		var sb strings.Builder
		sb.WriteString(strconv.Itoa(effectiveWidth))
		sb.WriteString("'b")
		digit := "0"
		if !pickMin { // Max value
			digit = "1"
		}
		for i := 0; i < effectiveWidth; i++ {
			sb.WriteString(digit)
		}
		return sb.String()

	case verilog.INTEGER, verilog.INT: // 32-bit signed
		if pickMin {
			return strconv.Itoa(math.MinInt32)
		}
		return strconv.Itoa(math.MaxInt32)

	case verilog.BYTE: // 8-bit
		if isSigned {
			if pickMin {
				return strconv.Itoa(math.MinInt8)
			}
			return strconv.Itoa(math.MaxInt8)
		}

		if pickMin {
			return "0"
		}
		return strconv.Itoa(math.MaxUint8)

	case verilog.SHORTINT: // 16-bit
		if isSigned {
			if pickMin {
				return strconv.Itoa(math.MinInt16)
			}
			return strconv.Itoa(math.MaxInt16)
		}

		if pickMin {
			return "0"
		}
		return strconv.Itoa(math.MaxUint16)

	case verilog.LONGINT: // 64-bit
		if isSigned {
			if pickMin {
				return strconv.FormatInt(math.MinInt64, 10)
			}
			return strconv.FormatInt(math.MaxInt64, 10)
		}

		if pickMin {
			return "0"
		}
		return strconv.FormatUint(math.MaxUint64, 10)

	case verilog.TIME: // 64-bit unsigned
		if pickMin {
			return "0"
		}
		return strconv.FormatUint(math.MaxUint64, 10)

	case verilog.REAL, verilog.REALTIME: // double precision
		if pickMin {
			if rand.Intn(2) == 0 {
				return "0.0"
			}
			return strconv.FormatFloat(-math.MaxFloat64, 'g', -1, 64)
		}
		return strconv.FormatFloat(math.MaxFloat64, 'g', -1, 64)

	case verilog.SHORTREAL: // single precision
		if pickMin {
			if rand.Intn(2) == 0 {
				return "0.0"
			}
			return strconv.FormatFloat(float64(-math.MaxFloat32), 'g', -1, 32)
		}
		return strconv.FormatFloat(float64(math.MaxFloat32), 'g', -1, 32)

	case verilog.STRING:
		if pickMin {
			return "\"\"" // Empty string
		}

		return "\"" + strings.Repeat("A", 20) + "\""

	case verilog.ENUM, verilog.STRUCT, verilog.USERDEFINED, verilog.VOID, verilog.UNKNOWN:
		effectiveWidth := width
		if effectiveWidth <= 0 {
			effectiveWidth = 1
		}
		if effectiveWidth > 1 {
			return strconv.Itoa(effectiveWidth) + "'bx"
		}
		return "'x"

	case verilog.TYPE:
		return ""

	default:
		return "'x"
	}
}
