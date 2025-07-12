module system_names_mod (
    input int in_val,
    output int out_val
);
    assign out_val = $bits(in_val);
endmodule

