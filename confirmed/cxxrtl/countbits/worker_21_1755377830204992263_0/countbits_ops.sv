module basic_assign_if (
    input logic in_a,
    input logic in_b,
    output logic out_c
);
    logic intermediate_wire;
    assign intermediate_wire = in_a & in_b;
    always_comb begin
        if (intermediate_wire) begin
            out_c = 1'b1;
        end else begin
            out_c = 1'b0;
        end
    end
endmodule

module case_parallel_simple_mod (
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        (* parallel *)
        case (case_inside_val)
            4'd0, 4'd1: internal_out = 14;
            4'd2, 4'd3: internal_out = 15;
            default: internal_out = 18;
        endcase
    end
endmodule

module countbits_ops (
    input wire clk,
    input logic [7:0] in_d,
    input logic [3:0] inj_case_inside_val_1755377830573_7,
    input logic inj_in_a_1755377830652_305,
    input logic inj_in_b_1755377830652_350,
    input logic [31:0] inj_p_in1_1755377830570_818,
    input logic [31:0] inj_p_in2_1755377830570_72,
    input logic [1:0] inj_p_mode_1755377830570_231,
    input wire rst,
    output logic [3:0] cnt,
    output logic [4:0] inj_internal_out_1755377830573_477,
    output logic inj_out_c_1755377830652_372,
    output logic [31:0] inj_p_out_1755377830570_901
);
    // BEGIN: more_procedural_ts1755377830570
    basic_assign_if basic_assign_if_inst_1755377830652_7210 (
        .in_a(inj_in_a_1755377830652_305),
        .in_b(inj_in_b_1755377830652_350),
        .out_c(inj_out_c_1755377830652_372)
    );
    case_parallel_simple_mod case_parallel_simple_mod_inst_1755377830573_2267 (
        .case_inside_val(inj_case_inside_val_1755377830573_7),
        .internal_out(inj_internal_out_1755377830573_477)
    );
    always_comb begin
        case (inj_p_mode_1755377830570_231)
            2'b00: inj_p_out_1755377830570_901 = (inj_p_in1_1755377830570_818 + inj_p_in2_1755377830570_72) * 2;
            2'b01: inj_p_out_1755377830570_901 = (inj_p_in1_1755377830570_818 - inj_p_in2_1755377830570_72) / 3; 
            2'b10: inj_p_out_1755377830570_901 = (inj_p_in1_1755377830570_818 << 4) | (inj_p_in2_1755377830570_72 >> 2);
            default: inj_p_out_1755377830570_901 = ~(inj_p_in1_1755377830570_818 ^ inj_p_in2_1755377830570_72) + 1;
        endcase
    end
    // END: more_procedural_ts1755377830570

    assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule

