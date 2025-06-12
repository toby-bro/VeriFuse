module PackedStructOps (
    input logic [7:0] byte_val,
    output logic [15:0] packed_out,
    output logic [7:0] byte_out,
    input logic [15:0] packed_in
);
    typedef struct packed {
        logic [7:0] low;
        logic [7:0] high;
    } pair_t;
    pair_t data_pair;
    assign data_pair = packed_in;
    assign byte_out = data_pair.high;
    assign data_pair.low = byte_val;
    assign packed_out = data_pair;
    assign packed_out[7:0] = data_pair.low + byte_val;
endmodule

