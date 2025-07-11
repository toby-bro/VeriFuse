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
    input bit dummy_in_fl,
    output enum_types::level_e first_val_out,
    output enum_types::level_e last_val_out
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
module EnumValueMethod_NextPrev (
    input enum_types::level_e current_val_np_in,
    input int count_in_np_in,
    input bit use_count_np_in,
    input bit select_next_np_in,
    input logic [7:0] non_member_int_np_in,
    input bit select_non_member_np_in,
    output enum_types::level_e result_val_np_out
);
    import enum_types::*;
    level_e temp_current_val;
    level_e result_val_reg_np;
    assign result_val_np_out = result_val_reg_np;
    always_comb begin
        if (select_non_member_np_in) begin
            temp_current_val = level_e'(non_member_int_np_in);
        end else begin
            temp_current_val = current_val_np_in;
        end
        if (select_next_np_in) begin
            if (use_count_np_in) begin
                result_val_reg_np = temp_current_val.next(count_in_np_in);
            end else begin
                result_val_reg_np = temp_current_val.next();
            end
        end else begin
            if (use_count_np_in) begin
                result_val_reg_np = temp_current_val.prev(count_in_np_in);
            end else begin
                result_val_reg_np = temp_current_val.prev();
            end
        end
    end
endmodule
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
module EnumValueMethod_Name (
    input enum_types::level_e value_in_name_in,
    input logic [7:0] non_enum_val_name_in,
    input bit select_enum_input_name_in,
    output string name_out_str_out
);
    import enum_types::*;
    level_e temp_val_name;
    string name_out_reg_name;
    assign name_out_str_out = name_out_reg_name;
    always_comb begin
        if (select_enum_input_name_in) begin
            temp_val_name = value_in_name_in;
        end else begin
            temp_val_name = level_e'(non_enum_val_name_in);
        end
        name_out_reg_name = temp_val_name.name();
    end
endmodule
