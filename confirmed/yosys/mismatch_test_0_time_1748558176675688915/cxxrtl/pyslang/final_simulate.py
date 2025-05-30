#!/usr/bin/env python3
import pyslang

# Create a script session
session = pyslang.ScriptSession()

print("Simulating SystemVerilog module: expr_postsub_comb")
print("Input values: in_val_m2 = 0xff, sub_val_m2 = 0x11")
print("=" * 50)

# Set up the variables with the exact values from the test case
session.eval("logic [7:0] in_val_m2 = 8'hff;")
session.eval("logic [7:0] sub_val_m2 = 8'h11;")
session.eval("logic [7:0] var_m2;")
session.eval("logic [7:0] out_diff_m2;")
session.eval("logic [7:0] var_out_m2;")

# Simulate the exact sequence from the always_comb block:
# always_comb begin
#   var_m2 = in_val_m2;
#   out_diff_m2 = (var_m2--) - sub_val_m2;
#   var_out_m2 = var_m2;
# end

print("\nStep 1: var_m2 = in_val_m2;")
session.eval('var_m2 = in_val_m2;')
var_m2_step1 = session.eval('var_m2')
print(f"  var_m2 = {var_m2_step1}")

print("\nStep 2: out_diff_m2 = (var_m2--) - sub_val_m2;")
session.eval('out_diff_m2 = (var_m2--) - sub_val_m2;')
out_diff_m2 = session.eval('out_diff_m2')
var_m2_step2 = session.eval('var_m2')
print(f"  out_diff_m2 = {out_diff_m2}")
print(f"  var_m2 (after post-decrement) = {var_m2_step2}")

print("\nStep 3: var_out_m2 = var_m2;")
session.eval('var_out_m2 = var_m2;')
var_out_m2 = session.eval('var_out_m2')
print(f"  var_out_m2 = {var_out_m2}")

# Display final results
print("\n" + "=" * 50)
print("SIMULATION RESULTS:")
print("=" * 50)

in_val_m2 = session.eval('in_val_m2')
sub_val_m2 = session.eval('sub_val_m2')

print(f"Inputs:")
print(f"  in_val_m2  = {in_val_m2}")
print(f"  sub_val_m2 = {sub_val_m2}")
print(f"\nOutputs:")
print(f"  out_diff_m2 = {out_diff_m2}")
print(f"  var_out_m2  = {var_out_m2}")

# Convert to hex for easier interpretation
def sv_to_hex(sv_val):
    """Convert SystemVerilog 8'd### format to hex"""
    str_val = str(sv_val)
    if str_val.startswith("8'd"):
        decimal_val = int(str_val[3:])
        return f"0x{decimal_val:02x}"
    return str_val

print(f"\nHexadecimal representation:")
print(f"  in_val_m2  = {sv_to_hex(in_val_m2)} ({str(in_val_m2)})")
print(f"  sub_val_m2 = {sv_to_hex(sub_val_m2)} ({str(sub_val_m2)})")
print(f"  out_diff_m2 = {sv_to_hex(out_diff_m2)} ({str(out_diff_m2)})")
print(f"  var_out_m2  = {sv_to_hex(var_out_m2)} ({str(var_out_m2)})")

print(f"\nExpected behavior analysis:")
print(f"  1. var_m2 starts as 0xff (255)")
print(f"  2. Post-decrement (var_m2--) uses current value in expression: 0xff - 0x11 = 0xee (238)")
print(f"  3. Then var_m2 is decremented to 0xfe (254)")
print(f"  4. var_out_m2 gets the decremented value: 0xfe (254)")

# Verify the results
expected_out_diff = 0xff - 0x11  # Should be 0xee = 238
expected_var_out = 0xff - 1       # Should be 0xfe = 254

actual_out_diff = int(str(out_diff_m2)[3:]) if str(out_diff_m2).startswith("8'd") else 0
actual_var_out = int(str(var_out_m2)[3:]) if str(var_out_m2).startswith("8'd") else 0

print(f"\nVerification:")
print(f"  Expected out_diff_m2 = {expected_out_diff} (0x{expected_out_diff:02x})")
print(f"  Actual   out_diff_m2 = {actual_out_diff} (0x{actual_out_diff:02x})")
print(f"  Expected var_out_m2  = {expected_var_out} (0x{expected_var_out:02x})")
print(f"  Actual   var_out_m2  = {actual_var_out} (0x{actual_var_out:02x})")

if actual_out_diff == expected_out_diff and actual_var_out == expected_var_out:
    print(f"  ✓ Results match expected behavior!")
else:
    print(f"  ✗ Results do not match expected behavior.")
