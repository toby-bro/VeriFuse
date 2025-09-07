module graph_struct_union (
    input logic [31:0] bus_in,
    input wire clk,
    input logic [7:0] inj_data_in_1755374690838_411,
    input logic inj_en_1755374690838_231,
    input logic [15:0] inj_packed_in_1755374690832_418,
    input wire rst,
    output logic [31:0] bus_out,
    output logic [7:0] inj_data_out_1755374690838_314,
    output logic [7:0] inj_field0_byte_o_1755374690832_197
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
    // BEGIN: typedef_union_mod_ts1755374690832
    typedef union packed {
        logic [15:0] word_ts1755374690832;
        logic [1:0][7:0] byte_fields_ts1755374690832;
    } my_packed_union_t;
    my_packed_union_t my_union_var;
    // BEGIN: sequential_register_en_ts1755374690870
    always_ff @(posedge clk) begin
        if (inj_en_1755374690838_231) begin
            inj_data_out_1755374690838_314 <= inj_data_in_1755374690838_411;
        end
    end
    // END: sequential_register_en_ts1755374690870

    always_comb begin
        my_union_var.word_ts1755374690832 = inj_packed_in_1755374690832_418;
    end
    assign inj_field0_byte_o_1755374690832_197 = my_union_var.byte_fields_ts1755374690832[0];
    // END: typedef_union_mod_ts1755374690832

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

