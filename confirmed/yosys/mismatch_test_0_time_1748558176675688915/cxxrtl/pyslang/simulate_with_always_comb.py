#!/usr/bin/env python3
"""
Python script to simulate the expr_postsub_comb.sv SystemVerilog module
using pyslang with an always_comb block to match the original structure.

Inputs: in_val_m2 = 0xff, sub_val_m2 = 0x11
"""

import pyslang

def main():
    # Create a script session
    session = pyslang.ScriptSession()
    
    print("Simulating expr_postsub_comb module with always_comb block")
    print("Inputs: in_val_m2 = 0xff, sub_val_m2 = 0x11")
    print("=" * 55)
    
    # Create a testbench that includes the always_comb block
    testbench_code = '''
    // Input signals
    logic [7:0] in_val_m2 = 8'hff;
    logic [7:0] sub_val_m2 = 8'h11;
    
    // Output signals
    logic [7:0] out_diff_m2;
    logic [7:0] var_out_m2;
    
    // Internal variable
    logic [7:0] var_m2;
    
    // Always_comb block that matches the original module
    always_comb begin
        var_m2 = in_val_m2;
        out_diff_m2 = (var_m2--) - sub_val_m2;
        var_out_m2 = var_m2;
    end
    '''
    
    print("Setting up testbench with always_comb block...")
    session.eval(testbench_code)
    
    # Force evaluation of the combinational logic
    print("Forcing combinational logic evaluation...")
    session.eval('#0;')  # Zero-delay to trigger combinational evaluation
    
    # Read the results
    print("\nReading simulation results...")
    
    try:
        in_val = session.eval('in_val_m2')
        sub_val = session.eval('sub_val_m2')
        out_diff = session.eval('out_diff_m2')
        var_out = session.eval('var_out_m2')
        var_internal = session.eval('var_m2')
        
        print(f"\nInput signals:")
        print(f"  in_val_m2  = {in_val}")
        print(f"  sub_val_m2 = {sub_val}")
        
        print(f"\nOutput signals:")
        print(f"  out_diff_m2 = {out_diff}")
        print(f"  var_out_m2  = {var_out}")
        
        print(f"\nInternal signal:")
        print(f"  var_m2 = {var_internal}")
        
        # Extract decimal values for hex display
        def extract_decimal(sv_str):
            if str(sv_str).startswith("8'd"):
                return int(str(sv_str)[3:])
            return 0
        
        in_val_dec = extract_decimal(in_val)
        sub_val_dec = extract_decimal(sub_val)
        out_diff_dec = extract_decimal(out_diff)
        var_out_dec = extract_decimal(var_out)
        var_internal_dec = extract_decimal(var_internal)
        
        print(f"\nHexadecimal representation:")
        print(f"  in_val_m2   = 0x{in_val_dec:02x} ({in_val_dec})")
        print(f"  sub_val_m2  = 0x{sub_val_dec:02x} ({sub_val_dec})")
        print(f"  out_diff_m2 = 0x{out_diff_dec:02x} ({out_diff_dec})")
        print(f"  var_out_m2  = 0x{var_out_dec:02x} ({var_out_dec})")
        print(f"  var_m2      = 0x{var_internal_dec:02x} ({var_internal_dec})")
        
        print(f"\n" + "=" * 55)
        print(f"ANALYSIS OF always_comb BEHAVIOR:")
        print(f"=" * 55)
        print(f"1. var_m2 = in_val_m2           → var_m2 = 0x{in_val_dec:02x}")
        print(f"2. out_diff_m2 = (var_m2--) - sub_val_m2")
        print(f"   - Uses current var_m2 value   → 0x{in_val_dec:02x} - 0x{sub_val_dec:02x} = 0x{out_diff_dec:02x}")
        print(f"   - Then decrements var_m2      → var_m2 becomes 0x{var_internal_dec:02x}")
        print(f"3. var_out_m2 = var_m2          → var_out_m2 = 0x{var_out_dec:02x}")
        
        # Verification
        expected_out_diff = (in_val_dec - sub_val_dec) & 0xFF
        expected_var_out = (in_val_dec - 1) & 0xFF
        
        print(f"\nVERIFICATION:")
        print(f"  Expected out_diff_m2 = 0x{expected_out_diff:02x}, Actual = 0x{out_diff_dec:02x} {'✓' if expected_out_diff == out_diff_dec else '✗'}")
        print(f"  Expected var_out_m2  = 0x{expected_var_out:02x}, Actual = 0x{var_out_dec:02x} {'✓' if expected_var_out == var_out_dec else '✗'}")
        
    except Exception as e:
        print(f"Error reading simulation results: {e}")
        print("This might indicate that the always_comb block evaluation failed.")

if __name__ == "__main__":
    main()
