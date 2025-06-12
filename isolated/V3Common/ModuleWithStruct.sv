module ModuleWithStruct (
    input logic [7:0] data_in,
    output int sum_out
);
    typedef struct {
        int field_a;
        logic [7:0] field_b;
        logic field_c;
    } MyStruct;
    MyStruct struct_var;
    int local_sum;
    always_comb begin
        struct_var.field_a = $unsigned(data_in);
        struct_var.field_b = data_in;
        struct_var.field_c = |data_in;
        local_sum = struct_var.field_a + $unsigned(struct_var.field_b);
        sum_out = local_sum;
    end
endmodule

