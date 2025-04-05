module combinatorial_logic (
    input  logic in1,
    input  logic in2,
    input  logic sel,
    output logic out
);
    // Combinatorial logic with mux
    always_comb begin
        case (sel)
            1'b0: out = in1 & in2;  // AND gate
            1'b1: out = in1 | in2;  // OR gate
        endcase
    end
endmodule
