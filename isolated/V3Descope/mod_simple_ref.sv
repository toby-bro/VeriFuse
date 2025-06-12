module mod_simple_ref (
    output logic o_result,
    input logic i_data
);
    logic internal_sig;
    always_comb begin
        internal_sig = i_data;
        o_result = internal_sig;
    end
endmodule

