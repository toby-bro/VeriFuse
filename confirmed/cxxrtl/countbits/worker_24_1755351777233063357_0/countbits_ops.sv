interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module mod_if_elseif_chained (
    input bit [7:0] in_value,
    output bit [2:0] out_category
);
always_comb begin
    if (in_value < 10) begin
        out_category = 3'd0;
    end else if (in_value < 50) begin
        out_category = 3'd1;
    end else if (in_value < 100) begin
        out_category = 3'd2;
    end else begin
        out_category = 3'd3;
    end
end
endmodule

module countbits_ops (
    input wire clk,
    input logic [7:0] in_d,
    input logic [7:0] inj_data_case_b_1755351777634_656,
    input bit [7:0] inj_in_value_1755351777633_372,
    input logic [1:0] inj_select_case_1755351777634_128,
    input wire rst,
    output logic [3:0] cnt,
    output logic inj_case_output_ready_1755351777634_844,
    output bit [2:0] inj_out_category_1755351777633_459
);
    // BEGIN: module_case_write_ts1755351777639
    my_if case_vif_inst();
    always_comb begin
        case (inj_select_case_1755351777634_128)
            2'b00: begin
                case_vif_inst.data = 8'hAA;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b0;
            end
            2'b01: begin
                case_vif_inst.data = in_d;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b1;
            end
            2'b10: begin
                case_vif_inst.data = inj_data_case_b_1755351777634_656;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b1;
            end
            default: begin
                case_vif_inst.data = 8'hFF;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b0;
            end
        endcase
        inj_case_output_ready_1755351777634_844 = case_vif_inst.ready;
    end
    // END: module_case_write_ts1755351777639

    mod_if_elseif_chained mod_if_elseif_chained_inst_1755351777633_2273 (
        .out_category(inj_out_category_1755351777633_459),
        .in_value(inj_in_value_1755351777633_372)
    );
    assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule

