module MiscExpressions_TaggedUnionParam (
    input logic in_dummy,
    output byte out_union_param_val
);
    typedef union tagged {
        byte b;
        int i;
    } param_union_t;
    parameter param_union_t p_u = tagged b 8'hFF; 
    assign out_union_param_val = p_u.b; 
endmodule

