module non_ansi_concat_port (
    concat_port_input,
    concat_port_output,
    non_ansi_i,
    non_ansi_j
);
    output logic [1:0] non_ansi_i;
    output logic [1:0] non_ansi_j;
    input logic concat_port_input;
    output logic concat_port_output;
    assign non_ansi_i = 2'b10;
    assign non_ansi_j = 2'b01;
    assign concat_port_output = concat_port_input;
endmodule

