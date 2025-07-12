package enum_types;
    typedef enum {
        E_NONE = 0,
        E_LOW = 10,
        E_MEDIUM = 20,
        E_HIGH = 30,
        E_MAX = 40
    } level_e;

endpackage

module EnumTypeMethods_FirstLast (
    input bit dummy_in_fl
);
    import enum_types::*;
    level_e first_val_reg;
    level_e last_val_reg;
    level_e dummy_enum_var;
    assign first_val_out = first_val_reg;
    assign last_val_out = last_val_reg;
    always_comb begin
        first_val_reg = dummy_enum_var.first();
        last_val_reg = dummy_enum_var.last();
    end
endmodule

