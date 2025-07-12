module GenerateFor (
    input logic [3:0] data_in,
    output logic [3:0] data_out
);
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : g_loop
            assign data_out[i] = data_in[i];
        end
    endgenerate
endmodule

