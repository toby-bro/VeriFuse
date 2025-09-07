module mod_automatic_task (
    input int i_val,
    output int o_val
);
    task automatic update_val(input int in_v, output int out_v);
        out_v = in_v * 2;
    endtask
    always_comb begin
        int temp_val;
        update_val(i_val, temp_val);
        o_val = temp_val;
    end
endmodule

module countbits_ops (
    input wire clk,
    input logic [7:0] in_d,
    input int inj_i_val_1755377830519_7,
    input logic [31:0] inj_in_1755377830518_867,
    input wire rst,
    output logic [3:0] cnt,
    output int inj_o_val_1755377830519_747,
    output logic [7:0] inj_out1_1755377830518_880,
    output logic inj_out2_1755377830518_117
);
    // BEGIN: constant_sel_ts1755377830518
    mod_automatic_task mod_automatic_task_inst_1755377830519_6757 (
        .i_val(inj_i_val_1755377830519_7),
        .o_val(inj_o_val_1755377830519_747)
    );
    assign inj_out1_1755377830518_880 = inj_in_1755377830518_867[15:8];
    assign inj_out2_1755377830518_117 = inj_in_1755377830518_867[3];
    // END: constant_sel_ts1755377830518

    assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule

