module index_packed_module (
    input wire [7:0] in2,
    output logic out2
);
    localparam bit [7:0] packed_array [3:0] = {8'h11, 8'h22, 8'h33, 8'h44};
    localparam bit [7:0] indexed_packed_array = packed_array[1];
    typedef struct packed {
        bit [3:0] a;
        bit [3:0] b;
    } packed_struct_t_idx;
    localparam packed_struct_t_idx packed_struct = 8'hAB;
    localparam bit [3:0] indexed_packed_struct_a = packed_struct.a;
    always_comb begin
        out2 = indexed_packed_array[0];
    end
    logic [7:0] _dummy_in = in2;
endmodule

