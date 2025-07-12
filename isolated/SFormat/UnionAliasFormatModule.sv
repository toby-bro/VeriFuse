module UnionAliasFormatModule (
    input bit in_select,
    output logic [31:0] out_dummy
);
    typedef union packed {
        logic [15:0] byte_val;
        logic [15:0] shortint_val;
    } packed_union_t;
    typedef union {
        int i;
        string s;
        real r;
    } unpacked_union_t;
    typedef packed_union_t packed_union_alias_t;
    typedef unpacked_union_t unpacked_union_alias_t;
    typedef int int_array_alias_t[2];
    localparam packed_union_t const_packed_union = 16'h0055;
    localparam packed_union_alias_t const_packed_union_alias = const_packed_union;
    localparam int_array_alias_t const_int_array_alias = '{10, 20};
    localparam packed_union_t const_packed_union_alt = 16'hABCD;
    localparam int_array_alias_t const_int_array_alias_alt = '{30, 40};
    string formatted_p_packed_union;
    string formatted_p_unpacked_union_int;
    string formatted_p_unpacked_union_str;
    string formatted_p_unpacked_union_unset;
    string formatted_p_packed_union_alias;
    string formatted_p_unpacked_union_alias;
    string formatted_p_int_array_alias;
    localparam string format_p = "%p";
    unpacked_union_t var_unpacked_union_int;
    unpacked_union_t var_unpacked_union_str;
    unpacked_union_t var_unpacked_union_unset;
    unpacked_union_alias_t var_unpacked_union_alias;
    unpacked_union_t var_unpacked_union_real;
    always_comb begin
        formatted_p_packed_union = "";
        formatted_p_unpacked_union_int = "";
        formatted_p_unpacked_union_str = "";
        formatted_p_unpacked_union_unset = "";
        formatted_p_packed_union_alias = "";
        formatted_p_unpacked_union_alias = "";
        formatted_p_int_array_alias = "";
        var_unpacked_union_int.i = 123;
        var_unpacked_union_str.s = "hello";
        if (in_select) begin
            var_unpacked_union_alias = var_unpacked_union_str;
            formatted_p_packed_union = $sformatf(format_p, const_packed_union);
            formatted_p_unpacked_union_int = $sformatf(format_p, var_unpacked_union_int);
            formatted_p_unpacked_union_str = $sformatf(format_p, var_unpacked_union_str);
            formatted_p_unpacked_union_unset = $sformatf(format_p, var_unpacked_union_unset);
            formatted_p_packed_union_alias = $sformatf(format_p, const_packed_union_alias);
            formatted_p_unpacked_union_alias = $sformatf(format_p, var_unpacked_union_alias);
            formatted_p_int_array_alias = $sformatf(format_p, const_int_array_alias);
        end else begin
            var_unpacked_union_real.r = 9.87;
            var_unpacked_union_alias = var_unpacked_union_real;
            formatted_p_packed_union = $sformatf(format_p, const_packed_union_alt);
            formatted_p_unpacked_union_int = $sformatf(format_p, var_unpacked_union_real);
            formatted_p_unpacked_union_str = $sformatf(format_p, var_unpacked_union_unset);
            formatted_p_unpacked_union_unset = $sformatf(format_p, var_unpacked_union_int);
            formatted_p_packed_union_alias = $sformatf(format_p, const_packed_union_alt);
            formatted_p_unpacked_union_alias = $sformatf(format_p, var_unpacked_union_alias);
            formatted_p_int_array_alias = $sformatf(format_p, const_int_array_alias_alt);
        end
        out_dummy = in_select;
    end
endmodule

