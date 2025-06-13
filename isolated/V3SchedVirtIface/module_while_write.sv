interface loop_if;
    logic [3:0] index;
    logic done;
    modport Ctrl (output index, output done);
    modport Report (input index, input done);
endinterface
module module_while_write (
    input logic enable_loop,
    input logic [3:0] start_index,
    output logic loop_active
);
    loop_if lif_inst();
    always_comb begin
        logic [3:0] i_local;
        i_local = 4'h0;
        loop_active = 1'b0;
        lif_inst.index = start_index;
        lif_inst.done = 1'b1;
        if (enable_loop) begin
            i_local = start_index;
            while (i_local < 10) begin
                lif_inst.index = i_local;
                lif_inst.done = 1'b0;
                i_local = i_local + 1;
                loop_active = 1'b1;
            end
            lif_inst.done = (i_local == 10);
        end else begin
            loop_active = 1'b0;
        end
    end
endmodule

