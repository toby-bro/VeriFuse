module basic_assign_if (
    input logic in_b,
    output logic out_c,
    input logic in_a
);
    logic intermediate_wire;
      assign intermediate_wire = in_a & in_b;
      always_comb begin
    if (intermediate_wire) begin
      out_c = 1'b1;
    end else begin
      out_c = 1'b0;
    end
      end
endmodule

