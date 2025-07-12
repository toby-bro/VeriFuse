module nets_alias_clocking (
    input logic i_clk,
    input logic i_data_sync,
    input logic i_reg_data,
    input wire i_wire_data,
    output logic o_reg_out,
    output wire o_wire_out
);
    wire  w_internal;
    logic r_internal;
    assign w_internal  = i_wire_data & i_reg_data;
    assign o_wire_out  = w_internal;
    always_ff @(posedge i_clk) r_internal <= i_data_sync;
    assign o_reg_out = r_internal;
endmodule

