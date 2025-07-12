module macro_line_continuation_user (
    input logic lc_en,
    output logic [15:0] lc_val
);
    `define MULTI_VAL                \
        16'hABCD
    `define ADD_FIVE(v)              \
        ((v) +                         \
            5)
    logic [15:0] value_reg;
    always_comb begin
        if (lc_en)
            value_reg = `MULTI_VAL;
        else
            value_reg = `ADD_FIVE(16'h0010);
    end
    assign lc_val = value_reg;
endmodule

