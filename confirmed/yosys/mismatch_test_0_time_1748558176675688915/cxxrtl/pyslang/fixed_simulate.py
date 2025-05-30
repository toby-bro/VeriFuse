#!/usr/bin/env python3
import pyslang

# Create a script session
session = pyslang.ScriptSession()

print("Testing post-decrement operation with pyslang ScriptSession...")

# Set up the variables with the exact values from the test
session.eval('''
logic [7:0] in_val_m2 = 8'hff;
logic [7:0] sub_val_m2 = 8'h11;
logic [7:0] var_m2;
logic [7:0] out_diff_m2;
logic [7:0] var_out_m2;
''')

# Simulate the exact sequence from the always_comb block
print("Step 1: var_m2 = in_val_m2")
session.eval('var_m2 = in_val_m2;')
var_before = session.eval('var_m2')
print(f"  var_m2 = {var_before}")

print("Step 2: out_diff_m2 = (var_m2--) - sub_val_m2")
# Try the post-decrement operation directly
try:
    session.eval('out_diff_m2 = (var_m2--) - sub_val_m2;')
    out_diff = session.eval('out_diff_m2')
    var_after = session.eval('var_m2')
    print(f"  out_diff_m2 = {out_diff}")
    print(f"  var_m2 after decrement = {var_after}")
except Exception as e:
    print(f"  Error with post-decrement: {e}")
    # Fall back to manual simulation
    print("  Falling back to manual simulation:")
    session.eval('out_diff_m2 = var_m2 - sub_val_m2;')
    session.eval('var_m2 = var_m2 - 1;')
    out_diff = session.eval('out_diff_m2')
    var_after = session.eval('var_m2')
    print(f"  out_diff_m2 = {out_diff}")
    print(f"  var_m2 after manual decrement = {var_after}")

print("Step 3: var_out_m2 = var_m2")
session.eval('var_out_m2 = var_m2;')
var_out = session.eval('var_out_m2')
print(f"  var_out_m2 = {var_out}")

print(f"\nFinal Results:")
in_val = session.eval('in_val_m2')
sub_val = session.eval('sub_val_m2')
out_diff = session.eval('out_diff_m2')
var_out = session.eval('var_out_m2')

print(f"Inputs:")
print(f"  in_val_m2  = {in_val}")
print(f"  sub_val_m2 = {sub_val}")
print(f"Outputs:")
print(f"  out_diff_m2 = {out_diff}")
print(f"  var_out_m2  = {var_out}")

print(f"\nExpected behavior for post-decrement (var_m2--):")
print(f"  1. var_m2 starts as 0xff (255)")
print(f"  2. Expression uses current value: 0xff - 0x11 = 0xee (238)")
print(f"  3. Then var_m2 is decremented to 0xfe (254)")
print(f"  4. var_out_m2 gets the decremented value: 0xfe (254)")
