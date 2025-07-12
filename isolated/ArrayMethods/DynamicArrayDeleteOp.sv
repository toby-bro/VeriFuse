module DynamicArrayDeleteOp (
    input logic dummy_in,
    output int dyn_array_size_after_delete,
    output int dyn_array_size_before_delete
);
    int dyn_arr[];
    always_comb begin
        dyn_arr = new[5]('{1, 2, 3, 4, 5});
        dyn_array_size_before_delete = dyn_arr.size();
        dyn_arr.delete();
        dyn_array_size_after_delete = dyn_arr.size();
    end
endmodule

