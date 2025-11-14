# IEEE 1800-2023 Analysis: Streaming Operator Width Handling

## CORRECTION: The Standard IS Well-Defined!

### Key Finding from Section 11.4.14

The IEEE 1800-2023 standard **IS** well-defined for this case. The critical paragraph states:

> "If the target represents a fixed-size variable that is wider than the stream, the stream shall be widened to match it by filling with zero bits on the right."

This means:
- ✅ The stream result is placed in the **MSBs** (left side)
- ✅ Zero bits are added to the **LSBs** (right side)

### Correct Behavior

For `logic [31:0] y = {<<{b}}` where `b` is 8 bits:
- Stream result (8 bits) → bits [31:24] (MSBs)
- Zero padding (24 bits) → bits [23:0] (LSBs)
- Result: `32'hFF000000` (for b=8'hFF)

### Simulator Correctness

| Simulator | Output | Correctness |
|-----------|--------|-------------|
| Verilator | `32'h000000FF` | ❌ **WRONG** - places stream in LSBs |
| Slang/CXXRTL | `32'hFF000000` | ✅ **CORRECT** - places stream in MSBs |
| Xcelium | `32'hFF000000` | ✅ **CORRECT** - places stream in MSBs |

### The Bug

**Verilator has a bug** in its implementation of streaming concatenation assignment to wider targets. It incorrectly places the stream result in the LSBs instead of the MSBs as required by the standard.

### Commercial Simulator Agreement

The user reports that "all commercial simulators gave the same results a5000000 (with different numbers of zeros)". This confirms that the commercial simulators (including Xcelium) correctly implement the standard, while Verilator does not.

## Conclusion

This is **NOT an underspecification** - it's a **clear bug in Verilator**. The IEEE 1800-2023 standard explicitly states that streams are widened by "filling with zero bits on the right", meaning the stream goes in the MSBs.
