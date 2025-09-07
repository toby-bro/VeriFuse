module deep_comb_assign_chain (
    input wire [15:0] dcac_start_val,
    output logic [15:0] dcac_end_val
);
    logic [15:0] t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    logic [15:0] t11, t12, t13, t14, t15, t16, t17, t18, t19, t20;
    logic [15:0] t21, t22, t23, t24, t25, t26, t27, t28, t29, t30;
    logic [15:0] t31, t32, t33, t34, t35, t36, t37, t38, t39, t40;
    always_comb begin
        t1 = dcac_start_val + 1;
        t2 = t1 * 2;
        t3 = t2 - 3;
        t4 = t3 ^ 4;
        t5 = t4 | 5;
        t6 = t5 & 6;
        t7 = t6 + 7;
        t8 = t7 - 8;
        t9 = t8 ^ 9;
        t10 = t9 | 10;
        t11 = t10 & 11;
        t12 = t11 + 12;
        t13 = t12 - 13;
        t14 = t13 ^ 14;
        t15 = t14 | 15;
        t16 = t15 + 16;
        t17 = t16 * 17;
        t18 = t17 - 18;
        t19 = t18 ^ 19;
        t20 = t19 | 20;
        t21 = t20 + 1;
        t22 = t21 * 2;
        t23 = t22 - 3;
        t24 = t23 ^ 4;
        t25 = t24 | 5;
        t26 = t25 & 6;
        t27 = t26 + 7;
        t28 = t27 - 8;
        t29 = t28 ^ 9;
        t30 = t29 | 10;
        t31 = t30 & 11;
        t32 = t31 + 12;
        t33 = t32 - 13;
        t34 = t33 ^ 14;
        t35 = t34 | 15;
        t36 = t35 + 16;
        t37 = t36 * 17;
        t38 = t37 - 18;
        t39 = t38 ^ 19;
        t40 = t39 | 20;
        dcac_end_val = t40;
    end
endmodule

module mod_event_implicit (
    input wire [3:0] data_in,
    output reg [3:0] data_out
);
    always @* begin
        data_out = data_in;
    end
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module countbits_ops #(
    parameter bit GEN = 1
) (
    input wire clk,
    input logic [7:0] in_d,
    input logic inj_a_1755327926594_927,
    input logic inj_b_1755327926594_559,
    input wire [3:0] inj_data_in_1755327926602_730,
    input wire [15:0] inj_in_packed_data_1755327926592_863,
    input wire rst,
    output logic [3:0] cnt,
    output reg [3:0] inj_data_out_1755327926602_312,
    output logic [15:0] inj_dcac_end_val_1755327926620_215,
    output wire [7:0] inj_out_byte_1755327926592_216,
    output logic inj_sig_out_1755327926769_346,
    output logic inj_sum_1755327926594_173
);
    // BEGIN: packed_struct_module_ts1755327926592
    typedef struct packed {
        logic [7:0] byte1_ts1755327926592;
        logic [7:0] byte2_ts1755327926592;
    } my_packed_struct_t;
    my_packed_struct_t data_struct;
    // BEGIN: GenerateIfParam_ts1755327926769
    generate
        if (GEN) begin : g_true
            assign inj_sig_out_1755327926769_346 = inj_a_1755327926594_927;
        end
        else begin : g_false
            assign inj_sig_out_1755327926769_346 = ~inj_a_1755327926594_927;
        end
    endgenerate
    // END: GenerateIfParam_ts1755327926769

    deep_comb_assign_chain deep_comb_assign_chain_inst_1755327926620_1118 (
        .dcac_end_val(inj_dcac_end_val_1755327926620_215),
        .dcac_start_val(inj_in_packed_data_1755327926592_863)
    );
    mod_event_implicit mod_event_implicit_inst_1755327926602_5403 (
        .data_out(inj_data_out_1755327926602_312),
        .data_in(inj_data_in_1755327926602_730)
    );
    simple_adder simple_adder_inst_1755327926594_5289 (
        .b(inj_b_1755327926594_559),
        .sum(inj_sum_1755327926594_173),
        .a(inj_a_1755327926594_927)
    );
    assign data_struct = inj_in_packed_data_1755327926592_863;
    assign inj_out_byte_1755327926592_216 = data_struct.byte1_ts1755327926592;
    // END: packed_struct_module_ts1755327926592

    assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule

