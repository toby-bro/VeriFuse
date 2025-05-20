module assert_property_mod (
    output logic prop_out,
    input logic clk,
    input logic data_in
);
    property p_data_simple_concurrent;
    @(posedge clk) data_in;
      endproperty
      assert property (p_data_simple_concurrent);
      always @(posedge clk) begin
    assert (data_in);
      end
      assign prop_out = data_in;
endmodule

