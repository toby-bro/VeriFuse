package fuzz

import (
	"math/rand"
)

// TestCase represents a test case for the branch predictor
type TestCase struct {
	FetchRdata uint32
	FetchPc    uint32
	FetchValid uint8
}

// Strategy defines an interface for different fuzzing strategies
type Strategy interface {
	GenerateTestCase(iteration int) TestCase
	Name() string
}

// SimpleStrategy implements a simple random testing strategy
type SimpleStrategy struct {
	seed int64
}

func (s *SimpleStrategy) Name() string {
	return "simple"
}

func (s *SimpleStrategy) GenerateTestCase(iteration int) TestCase {
	r := rand.New(rand.NewSource(s.seed + int64(iteration)))

	return TestCase{
		FetchRdata: uint32(r.Uint32()),
		FetchPc:    uint32(r.Uint32()),
		FetchValid: uint8(r.Intn(2)), // 0 or 1
	}
}

// OpcodeAwareStrategy implements a more targeted strategy that understands RISC-V opcodes
type OpcodeAwareStrategy struct {
	seed int64
}

func (s *OpcodeAwareStrategy) Name() string {
	return "opcode-aware"
}

func (s *OpcodeAwareStrategy) GenerateTestCase(iteration int) TestCase {
	r := rand.New(rand.NewSource(s.seed + int64(iteration)))

	// Generate random opcodes that make sense for branch prediction
	opcodes := []uint32{
		0x63, // BRANCH opcode (0x63)
		0x6F, // JAL opcode (0x6F)
		0x01, // Compressed instruction
		0x00, // Random other
	}

	// Pick an opcode type
	opcodeType := r.Intn(len(opcodes))
	baseInstr := uint32(0)

	switch opcodes[opcodeType] {
	case 0x63: // BRANCH
		// Build a BRANCH instruction with random fields
		imm := uint32(r.Intn(4096) - 2048) // Some random immediate
		rs1 := uint32(r.Intn(32))          // Source register
		rs2 := uint32(r.Intn(32))          // Source register
		funct3 := uint32(r.Intn(8))        // Branch type

		// Pack the fields into instruction format
		imm12_10_5 := (imm >> 5) & 0x7F
		imm4_1_11 := ((imm & 0x1E) | ((imm >> 11) & 0x1))

		baseInstr = (((imm >> 12) & 0x1) << 31) | // imm[12]
			(imm12_10_5 << 25) | // imm[10:5]
			(rs2 << 20) | // rs2
			(rs1 << 15) | // rs1
			(funct3 << 12) | // funct3
			(imm4_1_11 << 8) | // imm[4:1,11]
			0x63 // BRANCH opcode

	case 0x6F: // JAL
		// Build a JAL instruction
		imm := uint32(r.Intn(1048576) - 524288) // Some random immediate
		rd := uint32(r.Intn(32))                // Destination register

		// Pack fields into instruction format
		baseInstr = (((imm >> 20) & 0x1) << 31) | // imm[20]
			(((imm >> 1) & 0x3FF) << 21) | // imm[10:1]
			(((imm >> 11) & 0x1) << 20) | // imm[11]
			(((imm >> 12) & 0xFF) << 12) | // imm[19:12]
			(rd << 7) | // rd
			0x6F // JAL opcode

	case 0x01: // Compressed instruction
		// Construct a valid compressed branch or jump
		isJump := r.Intn(2) == 1
		if isJump {
			// C.J or C.JAL format
			baseInstr = (uint32(r.Intn(2)) << 15) | // Choose between C.J and C.JAL
				(uint32(3) << 13) | // funct3 = 3 for C.JAL, 1 for C.J
				(uint32(r.Intn(2048)) << 2) | // Random immediate
				0x01 // Compressed instruction marker
		} else {
			// C.BEQZ or C.BNEZ
			baseInstr = (uint32(r.Intn(2)+6) << 13) | // 6 for C.BEQZ, 7 for C.BNEZ
				(uint32(r.Intn(8)) << 10) | // Register rs1'
				(uint32(r.Intn(256)) << 2) | // Immediate
				0x01 // Compressed instruction marker
		}

	default: // Random instruction
		baseInstr = r.Uint32()
	}

	return TestCase{
		FetchRdata: baseInstr,
		FetchPc:    uint32(r.Intn(1048576)) * 4, // Align to 4-byte boundary
		FetchValid: 1,
	}
}

// MutationStrategy implements a mutation-based strategy that evolves test cases
type MutationStrategy struct {
	seed           int64
	lastMismatches []TestCase
	opCodeStrategy *OpcodeAwareStrategy
}

func (s *MutationStrategy) Name() string {
	return "mutation"
}

func (s *MutationStrategy) GenerateTestCase(iteration int) TestCase {
	r := rand.New(rand.NewSource(s.seed + int64(iteration)))

	// Initialize opcode strategy if needed
	if s.opCodeStrategy == nil {
		s.opCodeStrategy = &OpcodeAwareStrategy{seed: s.seed}
	}

	// Use different strategies based on whether we have previous mismatches
	if len(s.lastMismatches) == 0 || iteration < 10 {
		// Start with opcode-aware generation for the first few iterations
		return s.opCodeStrategy.GenerateTestCase(iteration)
	}

	// Select a previous mismatch to mutate
	baseCase := s.lastMismatches[r.Intn(len(s.lastMismatches))]
	testCase := baseCase

	// Apply random mutations
	switch r.Intn(4) {
	case 0:
		// Flip random bits in the instruction
		numBits := r.Intn(5) + 1
		for i := 0; i < numBits; i++ {
			bitPos := r.Intn(32)
			testCase.FetchRdata ^= (1 << bitPos)
		}
	case 1:
		// Modify the PC value
		testCase.FetchPc = baseCase.FetchPc + uint32(r.Intn(16)-8)*4
	case 2:
		// Toggle valid flag
		testCase.FetchValid = 1 - baseCase.FetchValid
	case 3:
		// Keep opcode, randomize other fields
		opcodeField := testCase.FetchRdata & 0x7F
		testCase.FetchRdata = (r.Uint32() & 0xFFFFFF80) | opcodeField
	}

	return testCase
}
