module dup_expr (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out1,
    output logic [7:0] out2
);
    logic [7:0] temp_add;
    logic [7:0] temp_mult;
    logic [7:0] inter1;
    logic [7:0] inter2;
    logic [7:0] complex_expr;
    always_comb begin
        temp_add = in1 + in2;
        out1 = temp_add;
        out2 = in1 + in2;
        inter1 = in1 * 2;
        inter2 = in2 * 2;
        temp_mult = inter1 + inter2;
        complex_expr = (in1 + in2) * (in1 - in2) + (in1 + in2);
        if (in1 > in2) begin
            out1 = temp_mult;
        end else begin
            out1 = temp_add;
        end
        if (in2 >= in1) begin
            out2 = temp_add;
        end else begin
            out2 = temp_mult;
        end
        out1 = out1 + complex_expr;
    end
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module countbits_ops (
    input wire clk,
    input logic [7:0] in_d,
    input logic [7:0] inj_b_aa_1755304956884_948,
    input logic [7:0] inj_c_aa_1755304956884_870,
    input logic inj_i_in_1755304956891_678,
    input logic [15:0] inj_in1_1755304956885_384,
    input logic [15:0] inj_in2_1755304956885_264,
    input logic inj_sel_1755304956885_332,
    input wire rst,
    output logic [3:0] cnt,
    output logic inj_o_out_1755304956891_544,
    output logic [15:0] inj_out1_1755304956885_225,
    output logic [7:0] inj_out1_1755304956889_463,
    output logic inj_out1_1755304956904_206,
    output logic [15:0] inj_out2_1755304956885_81,
    output logic [7:0] inj_out2_1755304956889_223,
    output logic [7:0] inj_x_aa_1755304956884_497,
    output logic [7:0] inj_y_aa_1755304956884_267,
    output logic [7:0] inj_z_aa_1755304956884_816
);
    // BEGIN: split_combo_blocking_ts1755304956884
    // BEGIN: procedural_complex_ts1755304956885
    logic [15:0] temp1_ts1755304956885;
    logic [15:0] temp2_ts1755304956885;
        // BEGIN: attributes_on_expr_port_ts1755304956891
        logic internal_sig_ts1755304956891;
            // BEGIN: ModuleLineDirective_ts1755304956909
            logic internal_sig_a_ts1755304956909;
            logic internal_sig_b_ts1755304956909;
            logic unused_line_var_ts1755304956909;
            `line 100 "virtual_file_A.sv" 1
            assign internal_sig_a_ts1755304956909 = internal_sig_ts1755304956891;
            `line 20 "virtual_file_B.sv" 1
            assign internal_sig_b_ts1755304956909 = ~internal_sig_a_ts1755304956909;
            assign unused_line_var_ts1755304956909 = 1'b1;
            `line 150 "virtual_file_A.sv" 2
            assign inj_out1_1755304956904_206 = internal_sig_b_ts1755304956909;
            `line 1 "original_file.sv" 0
            // END: ModuleLineDirective_ts1755304956909

        assign internal_sig_ts1755304956891 = inj_i_in_1755304956891_678 & inj_sel_1755304956885_332;
        simple_adder sa_inst(
            .a  (inj_i_in_1755304956891_678),
            (* fanout_limit = 10 *) .b(inj_sel_1755304956885_332),
            .sum(inj_o_out_1755304956891_544)
        );
        // END: attributes_on_expr_port_ts1755304956891

        dup_expr dup_expr_inst_1755304956889_2603 (
            .out1(inj_out1_1755304956889_463),
            .out2(inj_out2_1755304956889_223),
            .in1(in_d),
            .in2(inj_b_aa_1755304956884_948)
        );
    always_comb begin
        temp1_ts1755304956885 = (inj_in1_1755304956885_384 + inj_in2_1755304956885_264) * 10;
        if (inj_sel_1755304956885_332) begin
            temp2_ts1755304956885 = temp1_ts1755304956885 ^ (inj_in1_1755304956885_384 >>> 2);
            inj_out1_1755304956885_225 = temp2_ts1755304956885 & inj_in2_1755304956885_264;
        end else begin
            temp2_ts1755304956885 = temp1_ts1755304956885 | (inj_in2_1755304956885_264 <<< 3);
            inj_out1_1755304956885_225 = temp2_ts1755304956885 + inj_in1_1755304956885_384;
        end
        inj_out2_1755304956885_81 = temp1_ts1755304956885 - temp2_ts1755304956885;
    end
    // END: procedural_complex_ts1755304956885

    always @(*) begin
        inj_x_aa_1755304956884_497 = in_d + inj_b_aa_1755304956884_948;
        inj_y_aa_1755304956884_267 = inj_x_aa_1755304956884_497 - inj_c_aa_1755304956884_870;
        inj_z_aa_1755304956884_816 = in_d * inj_c_aa_1755304956884_870;
    end
    // END: split_combo_blocking_ts1755304956884

    assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule

