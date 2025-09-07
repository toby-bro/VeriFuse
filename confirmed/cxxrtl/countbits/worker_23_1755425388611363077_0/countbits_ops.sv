module simple_logic_a (
    input wire data_a,
    output wire data_b
);
    assign data_b = ~data_a;
endmodule

module split_vector_assign (
    input logic clk_y,
    input logic condition_y,
    input logic [7:0] in_val_y,
    output logic [7:0] out_vec_y
);
    always @(posedge clk_y) begin
        if (condition_y) begin
            out_vec_y[3:0] <= in_val_y[3:0];
            out_vec_y[7:4] <= in_val_y[7:4] + 1;
        end else begin
            out_vec_y <= 8'hFF;
        end
    end
endmodule

module countbits_ops (
    input wire clk,
    input logic [7:0] in_d,
    input logic inj_condition_y_1755425388970_81,
    input logic [2:0] inj_in_val_1755425388934_179,
    input wire rst,
    output logic [3:0] cnt,
    output wire inj_data_b_1755425388969_538,
    output reg inj_out_res_1755425388934_531,
    output logic [7:0] inj_out_vec_y_1755425388970_237
);
    // BEGIN: casez_xz_alt_ts1755425388934
    split_vector_assign split_vector_assign_inst_1755425388970_2889 (
        .in_val_y(in_d),
        .out_vec_y(inj_out_vec_y_1755425388970_237),
        .clk_y(clk),
        .condition_y(inj_condition_y_1755425388970_81)
    );
    simple_logic_a simple_logic_a_inst_1755425388969_7288 (
        .data_a(clk),
        .data_b(inj_data_b_1755425388969_538)
    );
    always_comb begin
        inj_out_res_1755425388934_531 = 1'b0;
        casez (inj_in_val_1755425388934_179)
            3'b1?z: inj_out_res_1755425388934_531 = 1'b1;
            3'b0z?: inj_out_res_1755425388934_531 = 1'b0;
            default: inj_out_res_1755425388934_531 = 1'b1;
        endcase
    end
    // END: casez_xz_alt_ts1755425388934

    assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule

