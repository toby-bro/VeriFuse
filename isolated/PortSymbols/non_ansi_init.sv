module non_ansi_init (
    non_ansi_init_input,
    non_ansi_init_output
);
    output logic non_ansi_g = 1'b1;
    output logic non_ansi_h = 1'b0;
    input logic non_ansi_init_input;
    output logic non_ansi_init_output;
    assign non_ansi_init_output = non_ansi_init_input;
endmodule

