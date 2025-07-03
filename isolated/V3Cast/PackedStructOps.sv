module PackedStructOps (
    input logic [7:0] byte_val,
    input logic [15:0] packed_in,
    output logic [7:0] byte_out,
    output logic [15:0] packed_out
);
    typedef struct packed {
        logic [7:0] low;
        logic [7:0] high;
    } pair_t;
    pair_t data_pair;
    assign data_pair.high = packed_in[15:8];
    assign data_pair.low = byte_val;
    assign byte_out = data_pair.high;
    assign packed_out[15:8] = data_pair.high;
    assign packed_out[7:0] = data_pair.low + byte_val;
endmodule

