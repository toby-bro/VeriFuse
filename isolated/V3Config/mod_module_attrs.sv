module mod_module_attrs #(
    parameter int WIDTH = 8
) (
    input wire [7:0] i_in,
    output logic [7:0] o_out
);
    logic [WIDTH-1:0] r_data;
    always_comb begin
        r_data = i_in;
    end
    assign o_out = r_data;
endmodule

