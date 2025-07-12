class default_arg_class;
    int member_offset;
    function new(input int offset = 0);
        member_offset = offset;
    endfunction
    function int add_with_default(input int x, input int y = 7);
        return x + y + member_offset;
    endfunction
endclass

class derived_default_arg_class extends default_arg_class;
    int extra_offset;
    function new(input int initial_offset = 0, input int extra = 5);
        super.new(initial_offset);
        extra_offset = extra;
    endfunction
    function int get_total_offset();
        return member_offset + extra_offset;
    endfunction
endclass

module default_args (
    input int derived_extra_in,
    input int offset_in,
    input int val1,
    input int val2,
    output int ctor_default_result,
    output int ctor_no_default_result,
    output int derived_ctor_default_inherit,
    output int derived_ctor_no_default_inherit,
    output int result_no_default,
    output int result_with_default
);
    default_arg_class inst_default;
    default_arg_class inst_no_default;
    default_arg_class inst_ctor_default;
    default_arg_class inst_ctor_no_default;
    derived_default_arg_class inst_derived_default;
    derived_default_arg_class inst_derived_no_default;
    always_comb begin
        if (inst_ctor_default == null) begin
            inst_ctor_default = new();
        end
        if (inst_ctor_no_default == null) begin
            inst_ctor_no_default = new(offset_in);
        end
            if (inst_default == null) begin
                inst_default = new(1);
        end
            if (inst_no_default == null) begin
                inst_no_default = new(2);
        end
        if (inst_derived_default == null) begin
            inst_derived_default = new(offset_in + 10, derived_extra_in);
        end
            if (inst_derived_no_default == null) begin
                inst_derived_no_default = new();
        end
        result_with_default = inst_default.add_with_default(val1);
        result_no_default = inst_no_default.add_with_default(val1, val2);
        ctor_default_result = inst_ctor_default.member_offset;
        ctor_no_default_result = inst_ctor_no_default.member_offset;
        derived_ctor_default_inherit = inst_derived_default.get_total_offset();
        derived_ctor_no_default_inherit = inst_derived_no_default.get_total_offset();
    end
endmodule

