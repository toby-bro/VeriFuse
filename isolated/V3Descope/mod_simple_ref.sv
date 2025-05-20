module mod_simple_ref (
    input logic i_data,
    output logic o_result
);
    logic internal_sig;
      always_comb begin
    internal_sig = i_data;
    o_result = internal_sig;
      end
endmodule

