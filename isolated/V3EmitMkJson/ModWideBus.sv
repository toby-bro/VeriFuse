module ModWideBus (
    input logic [31:0] data_in_w,
    output logic [31:0] data_out_w
);
    assign data_out_w = ~data_in_w;
endmodule

