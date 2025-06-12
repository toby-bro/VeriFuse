module Comb_Loop (
    output wire loop_out,
    input wire loop_in
);
    wire loop_wire1;
    wire loop_wire2;
    assign loop_wire1 = loop_wire2 | loop_in;
    assign loop_wire2 = loop_wire1; 
    assign loop_out = loop_wire1;
endmodule

