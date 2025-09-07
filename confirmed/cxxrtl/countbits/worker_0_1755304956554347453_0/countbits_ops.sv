interface cond_if;
    logic [15:0] control_reg;
    logic [15:0] status_reg;
    modport CtrlStat (output control_reg, input status_reg);
endinterface
interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module countbits_ops (
    input wire clk,
    input logic [7:0] in_d,
    input logic inj_data0_1755304956858_225,
    input logic inj_data1_1755304956858_180,
    input logic [15:0] inj_data_in_1755304956867_809,
    input int inj_in_val_1755304956862_68,
    input logic inj_sel_1755304956858_762,
    input wire rst,
    output logic [3:0] cnt,
    output logic inj_control_status_1755304956867_645,
    output logic inj_out_data_q_1755304956848_467,
    output int inj_out_val_1755304956862_657,
    output logic inj_result_1755304956858_997
);
    // BEGIN: module_assign_nonblocking_ts1755304956849
    my_if vif_inst();
    logic [7:0] data_q_ts1755304956849;
        // BEGIN: module_conditional_write_ts1755304956867
        cond_if cif_inst();
        always_comb begin
            if (inj_data0_1755304956858_225) begin
                cif_inst.control_reg = inj_data_in_1755304956867_809;
            end else begin
                cif_inst.control_reg = 16'h0;
            end
            inj_control_status_1755304956867_645 = (cif_inst.control_reg != 16'h0);
        end
        // END: module_conditional_write_ts1755304956867

        // BEGIN: super_outside_class_diag_mod_ts1755304956862
        assign inj_out_val_1755304956862_657 = inj_in_val_1755304956862_68;
        // END: super_outside_class_diag_mod_ts1755304956862

        // BEGIN: multiplexer_2to1_ts1755304956858
        assign inj_result_1755304956858_997 = inj_sel_1755304956858_762 ? inj_data1_1755304956858_180 : inj_data0_1755304956858_225;
        // END: multiplexer_2to1_ts1755304956858

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            vif_inst.data <= 8'h0;
            data_q_ts1755304956849 <= 8'h0;
        end else begin
            vif_inst.data <= in_d;
            data_q_ts1755304956849 <= vif_inst.data;
        end
    end
    assign inj_out_data_q_1755304956848_467 = data_q_ts1755304956849;
    // END: module_assign_nonblocking_ts1755304956849

    assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule

