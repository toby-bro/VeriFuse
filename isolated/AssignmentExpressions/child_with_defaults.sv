module child_with_defaults (
    output int out_int,
    output logic out_logic
);
    assign out_int = in_int_default;
    assign out_logic = in_logic_default;
endmodule

