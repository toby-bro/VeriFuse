module PulseStyleModule (
    input wire clk,
    input wire data_in_ps,
    output wire data_out_ps
);
    reg ff_q;
    always @(posedge clk) begin
        ff_q <= data_in_ps;
    end
    assign data_out_ps = ff_q;
    specify
        pulsestyle_ondetect data_out_ps;
        showcancelled        data_out_ps;
        (data_in_ps => data_out_ps) = (1, 1);
    endspecify
endmodule

