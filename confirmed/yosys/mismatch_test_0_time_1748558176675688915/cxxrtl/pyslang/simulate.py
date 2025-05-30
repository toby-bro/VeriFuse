#!/usr/bin/env python3
import pyslang

# Create a script session
session = pyslang.ScriptSession()

# Load the SystemVerilog file and create a compilation
print("Loading SystemVerilog file...")
tree = pyslang.SyntaxTree.fromFile('../../expr_postsub_comb.sv')
compilation = pyslang.Compilation()
compilation.addSyntaxTree(tree)

# Check if compilation succeeded
diagnostics = compilation.getAllDiagnostics()
if diagnostics:
    print("Compilation diagnostics:")
    for diag in diagnostics:
        print(f"  {diag}")

print("Creating testbench...")
# Create a simple testbench that manually computes the expected behavior
session.eval('''
logic [7:0] in_val_m2 = 8'hff;
logic [7:0] sub_val_m2 = 8'h11;
logic [7:0] var_m2;
logic [7:0] out_diff_m2;
logic [7:0] var_out_m2;
''')

# Manually simulate the always_comb behavior
print("Simulating the combinational logic...")
session.eval('var_m2 = in_val_m2;')  # var_m2 = 0xff

# The tricky part: (var_m2--) - sub_val_m2
# Post-decrement should use current value in expression, then decrement
session.eval('out_diff_m2 = var_m2 - sub_val_m2;')  # Use current value (0xff)
session.eval('var_m2 = var_m2 - 1;')  # Then decrement
session.eval('var_out_m2 = var_m2;')  # Output the decremented value

# Get the results
try:
    in_val = session.eval('in_val_m2')
    sub_val = session.eval('sub_val_m2')
    out_diff = session.eval('out_diff_m2')
    var_out = session.eval('var_out_m2')
    var_internal = session.eval('var_m2')
    
    print(f"\nSimulation Results:")
    print(f"Input values:")
    print(f"  in_val_m2  = {in_val} (0x{in_val.as_int():02x})")
    print(f"  sub_val_m2 = {sub_val} (0x{sub_val.as_int():02x})")
    print(f"\nOutput values:")
    print(f"  out_diff_m2 = {out_diff} (0x{out_diff.as_int():02x})")
    print(f"  var_out_m2  = {var_out} (0x{var_out.as_int():02x})")
    print(f"  var_m2 (internal) = {var_internal} (0x{var_internal.as_int():02x})")
    
    print(f"\nExpected behavior:")
    print(f"  var_m2 starts as 0xff (255)")
    print(f"  out_diff_m2 = (var_m2--) - sub_val_m2 = 0xff - 0x11 = 0xee (238)")
    print(f"  var_out_m2 = var_m2 after decrement = 0xfe (254)")
    
except Exception as e:
    print(f"Error accessing signals: {e}")

# Also try to parse and examine the original module
print(f"\nModule Analysis:")
try:
    root = compilation.getRoot()
    if root:
        # Find the module
        for member in root.members:
            if hasattr(member, 'name') and member.name == 'expr_postsub_comb':
                print(f"Found module: {member.name}")
                break
        else:
            print("Module not found, listing all members:")
            for i, member in enumerate(root.members):
                print(f"  Member {i}: {type(member)} - {getattr(member, 'name', 'unnamed')}")
    else:
        print("No root found in compilation")
except Exception as e:
    print(f"Error analyzing module: {e}")