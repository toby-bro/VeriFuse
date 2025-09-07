module graph_struct_union (
    input logic [31:0] bus_in,
    input wire clk,
    input logic [7:0] inj_in_data_1755349247825_180,
    input wire rst,
    output logic [31:0] bus_out,
    output logic [1:0] inj_out_bits_1755349247825_572
);
    typedef struct packed {
        logic [7:0] byte0;
        logic [7:0] byte1;
        logic [7:0] byte2;
        logic [7:0] byte3;
    } bytes_t;
    typedef union packed {
        logic  [31:0] word;
        bytes_t       bytes;
    } data_u;
    data_u din, dout;
    // BEGIN: cast_select_demo_ts1755349247826
    logic [7:0] internal_ts1755349247826;
    always_comb begin
        internal_ts1755349247826 = inj_in_data_1755349247825_180;
        inj_out_bits_1755349247825_572 = internal_ts1755349247826[3 -: 2];
    end
    // END: cast_select_demo_ts1755349247826

    always_comb begin
        din.word         = bus_in;
        dout.word        = 32'h0;
        dout.bytes.byte0 = din.bytes.byte3;
        dout.bytes.byte1 = din.bytes.byte2;
        dout.bytes.byte2 = din.bytes.byte1;
        dout.bytes.byte3 = din.bytes.byte0;
    end
    assign bus_out = dout.word;
endmodule

