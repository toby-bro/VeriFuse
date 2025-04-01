
module testbench;
    logic clk_i;
    logic rst_ni;
    logic [31:0] fetch_rdata_i;
    logic [31:0] fetch_pc_i;
    logic        fetch_valid_i;
    logic        predict_branch_taken_o;
    logic [31:0] predict_branch_pc_o;

    ibex_branch_predict dut (.*);

    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, testbench);
        
        // Read inputs from stdin
        $readmemh("input.hex", fetch_rdata_i);
        $readmemh("pc.hex", fetch_pc_i);
        $readmemb("valid.hex", fetch_valid_i);

        #1;
        
        // Write outputs to files
        $writememb("taken.hex", predict_branch_taken_o);
        $writememh("target.hex", predict_branch_pc_o);
        
        $finish;
    end
endmodule