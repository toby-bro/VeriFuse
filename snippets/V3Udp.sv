primitive combinational_udp_basic ( output out, input in1, in2 );
    table
        0   0  : 0;
        0   1  : 0;
        1   0  : 0;
        1   1  : 1;
    endtable
endprimitive
primitive sequential_udp_basic ( output reg out, input clk, data );
    table
        p   1  : ?           : 1;
        p   0  : ?           : 0;
        n   ?  : ?           : -;
        ?   ?  : ?           : -;
    endtable
endprimitive
primitive combinational_udp_wildcard ( output out, input in1, in2 );
    table
        0   ?  : 0;
        1   0  : 0;
        1   1  : 1;
    endtable
endprimitive
primitive sequential_udp_nochange ( output reg out, input clk, enable );
    table
        r   1   : ?           : 1;
        r   0   : ?           : -;
        *   ?   : ?           : -;
        ?   ?   : ?           : -;
    endtable
endprimitive
primitive combinational_udp_x ( output out, input in1, in2 );
    table
        0   0  : 0;
        0   1  : 1;
        1   0  : x;
        1   1  : 1;
    endtable
endprimitive
primitive sequential_udp_x ( output reg out, input clk, data );
    table
        p   0  : ?           : 0;
        p   1  : ?           : 1;
        p   x  : ?           : x;
        ?   ?  : ?           : -;
    endtable
endprimitive
primitive combinational_udp_dontcare_input ( output out, input in1, in2 );
    table
        -   0  : 0;
        1   1  : 1;
    endtable
endprimitive
module simple_and_gate (
    input logic in1,
    input logic in2,
    output logic out
);
    assign out = in1 & in2;
endmodule
module simple_xor_gate (
    input logic in1,
    input logic in2,
    output logic out
);
    assign out = in1 ^ in2;
endmodule
module basic_d_flipflop (
    input logic clk,
    input logic d,
    output logic q
);
    always_ff @(posedge clk) begin
        q <= d;
    end
endmodule
module multiplexer_2to1 (
    input logic data0,
    input logic data1,
    input logic sel,
    output logic result
);
    assign result = sel ? data1 : data0;
endmodule
module combinatorial_logic (
    input logic [3:0] in_vector,
    output logic out_single
);
    always_comb begin
        if (in_vector > 4'd5) begin
            out_single = 1'b1;
        end else begin
            out_single = 1'b0;
        end
    end
endmodule
module sequential_register_en (
    input logic clk,
    input logic en,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    always_ff @(posedge clk) begin
        if (en) begin
            data_out <= data_in;
        end
    end
endmodule
