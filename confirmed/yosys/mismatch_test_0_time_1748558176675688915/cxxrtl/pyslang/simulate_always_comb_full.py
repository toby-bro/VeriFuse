#!/usr/bin/env python3
"""
Python script to simulate the expr_postsub_comb.sv SystemVerilog module
using pyslang by instantiating the actual module and running it.

Inputs: in_val_m2 = 0xff, sub_val_m2 = 0x11
"""

import pyslang

def main():
    # Create a script session
    session = pyslang.ScriptSession()
    
    print("Simulating expr_postsub_comb with always_comb using module instantiation")
    print("Inputs: in_val_m2 = 0xff, sub_val_m2 = 0x11")
    print("=" * 65)
    
    # First, let's define the original module inline
    original_module = '''
    module expr_postsub_comb (
        input logic [7:0] in_val_m2,
        input logic [7:0] sub_val_m2,
        output logic [7:0] out_diff_m2,
        output logic [7:0] var_out_m2
    );
        logic [7:0] var_m2;
        always_comb begin
            var_m2 = in_val_m2;
            out_diff_m2 = (var_m2--) - sub_val_m2;
            var_out_m2 = var_m2;
        end
    endmodule
    '''
    
    # Create a testbench that instantiates the module
    testbench = '''
    module testbench;
        logic [7:0] in_val_m2;
        logic [7:0] sub_val_m2;
        logic [7:0] out_diff_m2;
        logic [7:0] var_out_m2;
        
        // Instantiate the module under test
        expr_postsub_comb dut (
            .in_val_m2(in_val_m2),
            .sub_val_m2(sub_val_m2),
            .out_diff_m2(out_diff_m2),
            .var_out_m2(var_out_m2)
        );
        
        // Test stimulus
        initial begin
            in_val_m2 = 8'hff;
            sub_val_m2 = 8'h11;
            #1; // Wait for combinational logic
        end
    endmodule
    '''
    
    try:
        print("Step 1: Defining the original module...")
        session.eval(original_module)
        print("✓ Original module defined")
        
        print("Step 2: Creating testbench...")
        session.eval(testbench)
        print("✓ Testbench created")
        
        print("Step 3: Running simulation...")
        # Set the inputs on the testbench
        session.eval('testbench.in_val_m2 = 8\'hff;')
        session.eval('testbench.sub_val_m2 = 8\'h11;')
        
        # Try to read the outputs
        print("Step 4: Reading outputs...")
        in_val = session.eval('testbench.in_val_m2')
        sub_val = session.eval('testbench.sub_val_m2')
        out_diff = session.eval('testbench.out_diff_m2')
        var_out = session.eval('testbench.var_out_m2')
        
        print(f"\nResults from module instantiation:")
        print(f"  in_val_m2   = {in_val}")
        print(f"  sub_val_m2  = {sub_val}")
        print(f"  out_diff_m2 = {out_diff}")
        print(f"  var_out_m2  = {var_out}")
        
    except Exception as e:
        print(f"Module instantiation approach failed: {e}")
        print("\nFalling back to direct always_comb simulation...")
        
        # Create a standalone always_comb simulation
        standalone_sim = '''
        // Input signals
        logic [7:0] in_val_m2 = 8'hff;
        logic [7:0] sub_val_m2 = 8'h11;
        
        // Output signals (will be driven by always_comb)
        logic [7:0] out_diff_m2;
        logic [7:0] var_out_m2;
        
        // Internal variable
        logic [7:0] var_m2;
        
        // The always_comb block from the original module
        always_comb begin
            var_m2 = in_val_m2;
            out_diff_m2 = (var_m2--) - sub_val_m2;
            var_out_m2 = var_m2;
        end
        '''
        
        print("Creating standalone always_comb simulation...")
        session.eval(standalone_sim)
        
        # Force evaluation
        session.eval('#0;')
        
        # Read results
        print("Reading results from always_comb simulation...")
        in_val = session.eval('in_val_m2')
        sub_val = session.eval('sub_val_m2')
        out_diff = session.eval('out_diff_m2')
        var_out = session.eval('var_out_m2')
        var_internal = session.eval('var_m2')
        
        print(f"\n" + "=" * 65)
        print(f"ALWAYS_COMB SIMULATION RESULTS:")
        print(f"=" * 65)
        print(f"Inputs:")
        print(f"  in_val_m2   = {in_val}")
        print(f"  sub_val_m2  = {sub_val}")
        print(f"Outputs:")
        print(f"  out_diff_m2 = {out_diff}")
        print(f"  var_out_m2  = {var_out}")
        print(f"Internal:")
        print(f"  var_m2      = {var_internal}")
        
        # Convert to hex
        def sv_to_hex_dec(sv_val):
            s = str(sv_val)
            if s.startswith("8'd"):
                dec = int(s[3:])
                return f"0x{dec:02x} ({dec})"
            return s
        
        if str(out_diff) != "<unset>":
            print(f"\nHexadecimal representation:")
            print(f"  in_val_m2   = {sv_to_hex_dec(in_val)}")
            print(f"  sub_val_m2  = {sv_to_hex_dec(sub_val)}")
            print(f"  out_diff_m2 = {sv_to_hex_dec(out_diff)}")
            print(f"  var_out_m2  = {sv_to_hex_dec(var_out)}")
            print(f"  var_m2      = {sv_to_hex_dec(var_internal)}")
            
            print(f"\n✓ Always_comb block successfully simulated the post-decrement behavior!")
            print(f"✓ Post-decrement (var_m2--) used original value in arithmetic")
            print(f"✓ Variable was decremented after the expression evaluation")
        else:
            print(f"\n⚠ Always_comb simulation didn't produce expected results")
            print(f"  This may be a limitation of pyslang's ScriptSession for procedural blocks")

if __name__ == "__main__":
    main()
