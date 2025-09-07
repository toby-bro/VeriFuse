module case_default (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b01: out_res = 1'b1;
            2'b10: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module dup_cond (
    input logic [3:0] control,
    input logic [7:0] data_a,
    input logic [7:0] data_b,
    output logic [7:0] result1,
    output logic [7:0] result2
);
    always_comb begin
        result1 = '0;
        result2 = '0;
        if (control[0]) begin
            result1 = data_a + data_b;
        end else begin
            result1 = data_a - data_b;
        end
        if (control[1]) begin
            result2 = data_a - data_b;
        end else begin
            result2 = data_a + data_b;
        end
        case (control[3:2])
            2'b00: result1 = data_a & data_b;
            2'b01: result1 = data_a | data_b;
            2'b10: result2 = data_a & data_b;
            2'b11: result2 = data_a | data_b;
            default: begin result1 = '0; result2 = '0; end
        endcase
        if (control[0] == control[1]) begin
            result1 = result1 + 1;
        end else if (control[2] != control[3]) begin
            result2 = result2 - 1;
        end
    end
endmodule

module param_local_port #(
    parameter int P_PORT_VAL = 25
) (
    input logic i_reset,
    output logic [7:0] o_sum
);
    localparam int LP_BODY_VAL = 125;
    localparam int LP_CALCULATED = P_PORT_VAL + LP_BODY_VAL;
    always_comb begin
        if (i_reset) begin
            o_sum = 0;
        end else begin
            o_sum = LP_CALCULATED;
        end
    end
endmodule

module m_caseeq_demo (
    input wire clk,
    input logic in,
    input logic [3:0] inj_control_1755304758505_57,
    input logic [7:0] inj_data_a_1755304758505_682,
    input logic [7:0] inj_data_b_1755304758505_655,
    input logic [1:0] inj_in_val_1755304758570_619,
    input wire rst,
    output logic eq,
    output logic [7:0] inj_o_sum_1755304758694_598,
    output logic inj_out_b_1755304758633_602,
    output reg inj_out_res_1755304758570_971,
    output logic [7:0] inj_result1_1755304758505_998,
    output logic [7:0] inj_result2_1755304758505_658,
    output logic neq
);
    logic tri_sig = 1'bz;
    // BEGIN: LintUnusedSignal_ts1755304758633
    logic unused_w_ts1755304758633; 
        param_local_port param_local_port_inst_1755304758694_5650 (
            .i_reset(rst),
            .o_sum(inj_o_sum_1755304758694_598)
        );
    assign inj_out_b_1755304758633_602 = in;
    // END: LintUnusedSignal_ts1755304758633

    case_default case_default_inst_1755304758570_8438 (
        .in_val(inj_in_val_1755304758570_619),
        .out_res(inj_out_res_1755304758570_971)
    );
    dup_cond dup_cond_inst_1755304758505_2928 (
        .control(inj_control_1755304758505_57),
        .data_a(inj_data_a_1755304758505_682),
        .data_b(inj_data_b_1755304758505_655),
        .result1(inj_result1_1755304758505_998),
        .result2(inj_result2_1755304758505_658)
    );
    assign eq  = (in === tri_sig); 
    assign neq = (in !== tri_sig); 
endmodule

