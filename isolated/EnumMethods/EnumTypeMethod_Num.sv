package enum_types;
    typedef enum {
        E_NONE = 0,
        E_LOW = 10,
        E_MEDIUM = 20,
        E_HIGH = 30,
        E_MAX = 40
    } level_e;

endpackage

module EnumTypeMethod_Num (
    input bit dummy_in_num,
    output int num_vals_out
);
    import enum_types::*;
    int num_vals_reg;
    level_e dummy_enum_var;
    assign num_vals_out = num_vals_reg;
    always_comb begin
        num_vals_reg = dummy_enum_var.num();
    end
endmodule

