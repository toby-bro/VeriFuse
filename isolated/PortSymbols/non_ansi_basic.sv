module non_ansi_basic (
    non_ansi_a,
    non_ansi_basic_input,
    non_ansi_b,
    non_ansi_basic_output
);
    input wire non_ansi_a;
    output reg non_ansi_b;
    input logic non_ansi_basic_input;
    output logic non_ansi_basic_output;
    always_comb begin
        non_ansi_b = non_ansi_a;
        non_ansi_basic_output = non_ansi_basic_input;
    end
endmodule

