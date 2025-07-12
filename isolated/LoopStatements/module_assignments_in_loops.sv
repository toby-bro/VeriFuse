module module_assignments_in_loops (
    input logic [2:0] in_shift,
    input logic [7:0] in_val,
    output logic [3:0] out_part,
    output logic [7:0] out_reg
);
    localparam int PART_START = 4;
    localparam int PART_WIDTH = 4;
    logic [7:0] reg_var;
    logic [3:0] part_var;
    always_comb begin
        reg_var  = in_val;
        part_var = 4'h0;
        for (int i = 0; i < 4; i++) begin
            reg_var  = reg_var + i;
            reg_var += (i * 2);
            reg_var <<= in_shift;
            reg_var[i % 8] = (reg_var[i % 8] == 1'b0);
            reg_var[PART_START +: PART_WIDTH] = i[3:0];
        end
        part_var = reg_var[7:4];
    end
    assign out_reg  = reg_var;
    assign out_part = part_var;
endmodule

