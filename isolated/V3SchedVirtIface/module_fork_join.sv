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
module module_fork_join (
    input logic [7:0] data_a,
    input logic [7:0] data_b,
    output logic fork_status,
    input logic fork_en
);
    my_if vif_split();
      always_comb begin
    fork_status = 1'b0;
    vif_split.data = 8'h0;
    vif_split.ready = 1'b0;
    vif_split.valid = 1'b0;
    if (fork_en) begin
      fork
        vif_split.data = data_a;
        vif_split.ready = 1'b1;
      join_none
      fork_status = 1'b1;
    end else begin
        fork_status = 1'b0;
    end
      end
endmodule

