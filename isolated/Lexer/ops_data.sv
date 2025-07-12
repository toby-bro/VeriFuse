module ops_data (
    input logic [7:0] a,
    input logic [7:0] b,
    output logic flag,
    output logic [7:0] result
);
    typedef union packed {
        logic [15:0] word;
        logic [1:0][7:0] bytes;
    } word_byte_u;
    logic [7:0] mem [0:7];
    word_byte_u u;
    logic [7:0] tmp;
    logic [7:0] vec;
    logic [3:0] slice;
    always_comb begin
        vec   = a ^ b;
        slice = vec[3 -: 4];
        tmp   = (a + b) & 8'hFF;
        mem[a[2:0]] = tmp;
        u.word = {a, b};
        result = mem[a[2:0]] ^ u.bytes[0];
        flag = (result === 8'h00) ? 1'b1 : 1'b0;
    end
endmodule

