module nested_macro_expansion (
    input int in_val,
    output int out_val
);
    `define LVL1(x) ((x) + 1)
    `define LVL2(y) `LVL1((y) * 2)
    `define LVL3(z) `LVL2((z) / 3)
    int nested_result;
    always_comb begin
        nested_result = `LVL3(`LVL1(in_val));
    end
    assign out_val = nested_result;
endmodule

