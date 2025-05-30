#!/usr/bin/env python3
"""
Simple Python script to simulate the expr_postsub_comb.sv SystemVerilog module
using pyslang with the specified inputs:
- in_val_m2 = 0xff (255)
- sub_val_m2 = 0x11 (17)
"""

import pyslang

def main():
    # Create a script session
    session = pyslang.ScriptSession()
    
    print("Simulating expr_postsub_comb module with pyslang")
    print("Inputs: in_val_m2 = 0xff, sub_val_m2 = 0x11")
    print("-" * 45)
    
    # Declare variables and set input values
    session.eval("logic [7:0] in_val_m2 = 8'hff;")    # 255
    session.eval("logic [7:0] sub_val_m2 = 8'h11;")   # 17
    session.eval("logic [7:0] var_m2;")
    session.eval("logic [7:0] out_diff_m2;")
    session.eval("logic [7:0] var_out_m2;")
    
    # Simulate the always_comb block behavior:
    # always_comb begin
    #   var_m2 = in_val_m2;
    #   out_diff_m2 = (var_m2--) - sub_val_m2;
    #   var_out_m2 = var_m2;
    # end
    
    session.eval('var_m2 = in_val_m2;')
    session.eval('out_diff_m2 = (var_m2--) - sub_val_m2;')
    session.eval('var_out_m2 = var_m2;')
    
    # Get results
    in_val = session.eval('in_val_m2')
    sub_val = session.eval('sub_val_m2')
    out_diff = session.eval('out_diff_m2')
    var_out = session.eval('var_out_m2')
    
    # Display results
    print(f"Input values:")
    print(f"  in_val_m2  = {in_val}")
    print(f"  sub_val_m2 = {sub_val}")
    print(f"Output values:")
    print(f"  out_diff_m2 = {out_diff}")
    print(f"  var_out_m2  = {var_out}")
    
    # Convert to decimal for verification
    def extract_decimal(sv_str):
        if str(sv_str).startswith("8'd"):
            return int(str(sv_str)[3:])
        return 0
    
    out_diff_dec = extract_decimal(out_diff)
    var_out_dec = extract_decimal(var_out)
    
    print(f"\nIn hexadecimal:")
    print(f"  out_diff_m2 = 0x{out_diff_dec:02x} ({out_diff_dec})")
    print(f"  var_out_m2  = 0x{var_out_dec:02x} ({var_out_dec})")

if __name__ == "__main__":
    main()
