module StrengthAssign (
    input wire data_h,
    input wire data_l,
    output wire out_strength
);
    tri strength_wire;
    assign (pull1, pull0) strength_wire = data_h;
    assign (weak1, weak0) strength_wire = data_l;
    assign out_strength = strength_wire;
endmodule

