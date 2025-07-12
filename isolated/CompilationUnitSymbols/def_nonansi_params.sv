module def_nonansi_params (
    control_in,
    data_in_nonansi,
    control_out,
    data_out_nonansi
);
    parameter int VAL_PARAM = 10;
    localparam type TYPE_PARAM = int;
    input [VAL_PARAM-1:0] data_in_nonansi;
    output logic [VAL_PARAM-1:0] data_out_nonansi;
    input logic control_in;
    output logic control_out;
    TYPE_PARAM internal_val;
    always_comb begin
        data_out_nonansi = data_in_nonansi;
        control_out = control_in;
        internal_val = VAL_PARAM;
    end
endmodule

