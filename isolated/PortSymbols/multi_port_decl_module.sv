module multi_port_decl_module (
    input logic [3:0] p_a,
    input logic [3:0] p_b,
    input logic single_in,
    output logic single_out
);
    always_comb begin
        single_out = single_in;
    end
endmodule

