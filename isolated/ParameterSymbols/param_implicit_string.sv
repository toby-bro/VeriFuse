module param_implicit_string (
    input logic [1:0] i_char_index,
    output logic [7:0] o_ascii_char
);
    parameter IMPLICIT_STR = "System";
    parameter string EXPLICIT_STR = "Verilog";
    always_comb begin
        if (i_char_index < $size(IMPLICIT_STR)) begin
            o_ascii_char = IMPLICIT_STR[i_char_index];
        end else begin
            o_ascii_char = EXPLICIT_STR[0];
        end
    end
endmodule

