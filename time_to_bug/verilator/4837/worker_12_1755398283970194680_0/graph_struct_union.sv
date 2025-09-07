module graph_struct_union (
    input logic [31:0] bus_in,
    input wire clk,
    input logic inj_en_1755398284271_120,
    input logic [7:0] inj_in1_1755398284270_206,
    input logic [7:0] inj_in2_1755398284270_577,
    input wire rst,
    output logic [31:0] bus_out,
    output logic [7:0] inj_data_out_1755398284271_538,
    output logic [7:0] inj_out1_1755398284270_451
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
    // BEGIN: basic_comb_ts1755398284270
    ;
    logic [7:0] temp_wire_ts1755398284270;
    // BEGIN: sequential_register_en_ts1755398284271
    always_ff @(posedge clk) begin
        if (inj_en_1755398284271_120) begin
            inj_data_out_1755398284271_538 <= inj_in2_1755398284270_577;
        end
    end
    // END: sequential_register_en_ts1755398284271

    assign temp_wire_ts1755398284270 = inj_in1_1755398284270_206 + inj_in2_1755398284270_577;
    always_comb begin
        inj_out1_1755398284270_451 = temp_wire_ts1755398284270;
    end
    // END: basic_comb_ts1755398284270

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

