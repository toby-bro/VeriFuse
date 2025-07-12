module specify_edge (
    input wire clk,
    output wire q
);
    reg state;
    assign q = state;
    always @(posedge clk) state <= ~state;
    specparam edge_delay = 3;
    specify
        (posedge clk => q) = edge_delay;
    endspecify
endmodule

