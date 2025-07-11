`timescale 1ns/1ps
timeunit 1ns;
timeprecision 1ps;
`define SIMPLE_MACRO_VALUE 8'h55
`define CAT(a,b) a``b
`define WITH_ARGS(x,y) ((x)+(y))
module ops_data
(
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] result,
    output logic       flag
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
module literals_types
(
    input  logic [7:0] in_val,
    output logic [15:0] out_val
);
    logic [7:0]  byte_lit;
    logic [15:0] word_lit;
    real         r_val;
    time         t_val;
    always_comb begin
        byte_lit = '0;
        byte_lit = 8'b1010_1100;
        word_lit = 16'hDEAD;
        r_val    = 3.14e2;
        t_val    = 10ns;
        out_val  = {byte_lit, word_lit[7:0]};
        if (in_val inside {8'h00, 8'hFF, [8'h10:8'h20]})
            out_val = 16'h1234;
    end
endmodule
module macro_usage
(
    input  logic [7:0] sel,
    output logic [7:0] out_mac
);
    logic [7:0] temp_val;
    `define PREFIX foo_
    `define SUFFIX _bar
    logic [7:0] `CAT(PREFIX,SUFFIX);
    always_comb begin
        temp_val = `WITH_ARGS(sel, `SIMPLE_MACRO_VALUE);
        `CAT(PREFIX,SUFFIX) = temp_val;
        out_mac = `CAT(PREFIX,SUFFIX);
    end
endmodule
