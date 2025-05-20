module mod_assign_delay (
    output logic out,
    input logic in
);
    assign #3 out = in;
endmodule

