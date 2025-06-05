interface loop_if;
    logic [3:0] index;
    logic done;

    modport Ctrl (
        output index,
        output output done
    );

    modport Report (
        input index,
        input input done
    );

    logic [3:0] index;
      logic done;
      modport Ctrl (output index, output done);
      modport Report (input index, input done);
endinterface
module module_for_write (
    input logic enable_for,
    input logic [3:0] limit,
    output logic for_completed
);
    loop_if lif_for();
      always_comb begin
    logic [3:0] i;
    for_completed = 1'b0;
    lif_for.index = 4'h0;
    lif_for.done = 1'b0;
    if (enable_for) begin
      for (i = 0; i < limit; i = i + 1) begin
        lif_for.index = i;
        lif_for.done = 1'b0;
      end
      lif_for.done = 1'b1;
      for_completed = 1'b1;
    end else begin
        for_completed = 1'b0;
    end
      end
endmodule

