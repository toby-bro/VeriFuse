module ArrayReductionOps (
    input logic [7:0] in_val,
    output logic [31:0] out_and_fixed,
    output logic [31:0] out_or_fixed,
    output logic [31:0] out_product_fixed,
    output logic [31:0] out_sum_assoc,
    output logic [31:0] out_sum_dynamic,
    output logic [31:0] out_sum_fixed,
    output logic [31:0] out_sum_queue,
    output logic [31:0] out_xor_fixed
);
    int fixed_arr[5];
    int dynamic_arr[];
    int queue_arr[$];
    int assoc_arr[string];
    always_comb begin
        fixed_arr = '{1, 2, 3, 4, 5};
        dynamic_arr = new[3]('{6, 7, 8});
        queue_arr = {9, 10, 11};
        assoc_arr.delete(); 
        assoc_arr["a"] = 12;
        assoc_arr["b"] = 13;
        out_sum_fixed = fixed_arr.sum();
        out_sum_dynamic = dynamic_arr.sum();
        out_sum_queue = queue_arr.sum();
        out_sum_assoc = assoc_arr.sum();
        out_product_fixed = fixed_arr.product();
        out_or_fixed = fixed_arr.or();
        out_and_fixed = fixed_arr.and();
        out_xor_fixed = fixed_arr.xor();
        dynamic_arr = new[0];
        queue_arr = {};
        assoc_arr.delete();
        out_sum_dynamic = dynamic_arr.sum(); 
        out_sum_queue = queue_arr.sum();     
        out_sum_assoc = assoc_arr.sum();     
    end
endmodule

