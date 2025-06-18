interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module module_sequential_writes (
    input logic [7:0] addr,
    input logic [7:0] wdata,
    output logic write_status
);
    my_if vif_bus();
    always_comb begin
        vif_bus.data = wdata;
        vif_bus.ready = 1'b1;
        vif_bus.valid = 1'b0;
        write_status = vif_bus.ready;
    end
endmodule

