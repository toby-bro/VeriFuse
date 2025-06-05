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
module module_assign_blocking (
    input logic [7:0] in_data,
    output logic out_valid_status
);
    my_if vif_inst();
      always_comb begin
    vif_inst.data = in_data;
    vif_inst.valid = 1'b1;
    vif_inst.ready = 1'b0;
    out_valid_status = vif_inst.valid;
      end
endmodule

