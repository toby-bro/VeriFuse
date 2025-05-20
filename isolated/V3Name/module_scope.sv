module module_scope (
    input wire [7:0] s_input_val,
    output logic [7:0] s_output_val
);
    always @* begin : procedural_scope_block
    automatic logic [7:0] local_automatic_reg;
    if (s_input_val > 50) begin
      local_automatic_reg = s_input_val - 10;
    end else begin
      local_automatic_reg = s_input_val + 20;
    end
    s_output_val = local_automatic_reg;
      end : procedural_scope_block
endmodule

