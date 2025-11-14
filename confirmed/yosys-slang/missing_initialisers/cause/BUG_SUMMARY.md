# Root Cause Summary: Variable Initializer Bug in Yosys Slang Frontend

## Bug Description
The Yosys Slang frontend fails to synthesize variable initialization expressions into hardware logic.

## Minimal Test Case
```systemverilog
logic [3:0] inc_a = in_a + 4'd1;  // Initializer expression
logic [3:0] dec_b = in_b - 4'd1;  // Initializer expression
```

## Expected Behavior (SystemVerilog Semantics)
Variable declarations with initializers should be treated as:
```systemverilog
logic [3:0] inc_a;
assign inc_a = in_a + 4'd1;  // Continuous assignment
```

## What Native Yosys Does (CORRECT)
1. Parses: `logic [3:0] inc_a = in_a + 4'd1;`
2. Creates RTLIL:
   - Wire declaration: `wire width 4 \inc_a`
   - Add cell: `cell $add` (computes `in_a + 1`)
   - Process: Drives `inc_a` with result
3. After synthesis: `assign inc_a = in_a + 4'h1;`

## What Slang Frontend Does (BROKEN)
1. Parses: `logic [3:0] inc_a = in_a + 4'd1;`
2. Creates RTLIL:
   - Wire declaration: `wire width 4 \inc_a`
   - **NOTHING ELSE!**
3. After synthesis: `inc_a` is undriven (stuck at 'x')
4. Yosys warns: "Wire ph_conditional.\inc_a has no driver"

## Evidence Files

### RTLIL Comparison
- `native.il` - Shows `$add` cell and process block driving `inc_a`
- `slang.il` - Shows only wire declaration, no drivers

### Synthesized Verilog Comparison  
- `native_synth.v` - Contains `assign inc_a = _02_;` and `assign _02_ = in_a + 4'h1;`
- `slang_synth.v` - Wire `inc_a` declared but never assigned

### Test Results
With inputs `in_a=0, in_b=13, sel1=0, sel2=0`:
- Expected: `out_y = dec_b = 13-1 = 12 = 0b1100`
- Native Yosys: `0b1100` ✓
- Slang: `0b0000` ✗ (undriven wires read as 0 or 'x')

## Root Cause Location
The bug is in the Yosys Slang frontend module (`yosys-slang` plugin), specifically in the code that converts Slang's AST representation into Yosys RTLIL.

The conversion step that should:
1. Recognize variable declarations with initializer expressions
2. Generate appropriate cells (`$add`, `$sub`, etc.) for the expression
3. Generate a process or connection to drive the variable wire

...is either missing or not handling this case correctly.

## Impact
Any SystemVerilog design using variable initialization syntax:
```systemverilog
logic [N:0] var = <expression>;
```

Will be incorrectly synthesized, with `var` being undriven and stuck at an unknown value.

This is a critical bug as variable initialization is common SystemVerilog syntax.

## Recommended Fix
The Yosys Slang frontend needs to be modified to:
1. Detect variable declarations with initializers
2. Generate equivalent continuous assignment logic in RTLIL
3. Follow the same pattern as the native Yosys frontend (see `native.il`)

## Files for Bug Report
All files in this directory demonstrate and document the bug:
- `ph_conditional.sv` - Minimal reproducer
- `native.il` vs `slang.il` - RTLIL comparison
- `native_synth.v` vs `slang_synth.v` - Synthesis output comparison
- `compare_synth.sh` - Automated comparison script
- This README and VISUAL_COMPARISON.md - Full documentation
