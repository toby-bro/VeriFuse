module member_access_packed_union (
    input logic [31:0] in_val,
    input bit select_a,
    output logic [31:0] out_val
);
    typedef union packed {
        logic [31:0] a; 
        logic [31:0] b; 
    } my_packed_union;
    my_packed_union union_var;
    always_comb begin
        if (select_a)
            union_var.a = in_val;
        else
            union_var.b = in_val[31:0];
        out_val = union_var.a;
    end
endmodule

