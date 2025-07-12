class conversion_object;
    int val;
    function new(int v);
        val = v;
    endfunction
endclass

module NumericConversions (
    input logic signed [31:0] in_signed32,
    input logic [7:0] in_unsigned8,
    output logic signed [63:0] out_signed64_widen,
    output logic signed [7:0] out_signed8_sign_cast,
    output logic [15:0] out_unsigned16_narrow
);
    conversion_object dummy;
    always_comb begin
        out_signed64_widen    = in_signed32;
        out_unsigned16_narrow = 16'(in_unsigned8);
        out_signed8_sign_cast = signed'(in_unsigned8);
        dummy = new(0);
    end
endmodule

