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
module module_sequential_writes (
    output logic write_status,
    input logic [7:0] addr,
    input logic [7:0] wdata
);
    my_if vif_bus();
      always_comb begin
    vif_bus.data = wdata;
    vif_bus.ready = 1'b1;
    vif_bus.valid = 1'b0;
    write_status = vif_bus.ready;
      end
endmodule

