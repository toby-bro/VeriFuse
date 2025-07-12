module udnt_port_module (
    input logic udnt_input,
    input logic uin,
    output logic udnt_output,
    output logic uout
);
    assign uout = uin;
    assign udnt_output = udnt_input;
endmodule

