interface my_if;
    logic valid;
    logic [7:0] data;
    logic ready;

    modport FullAccess (
        input data,
        input output ready,
        input output valid
    );

    modport AccessIn (
        output data,
        output output valid,
        output input ready
    );

    modport AccessOut (
        input data,
        input input valid,
        input output ready
    );

    logic [7:0] data;
      logic ready;
      logic valid;
      modport FullAccess (input data, output ready, output valid);
      modport AccessIn (output data, output valid, input ready);
      modport AccessOut (input data, input valid, output ready);
endinterface
module module_assign_nonblocking (
    input logic reset,
    input logic [7:0] in_value,
    output logic out_data_q,
    input logic clk
);
    my_if vif_inst();
      logic [7:0] data_q;
      always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      vif_inst.data <= 8'h0;
      data_q <= 8'h0;
    end else begin
      vif_inst.data <= in_value;
      data_q <= vif_inst.data;
    end
      end
      assign out_data_q = data_q;
endmodule

