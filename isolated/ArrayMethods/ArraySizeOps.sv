module ArraySizeOps (
    input logic dummy_in,
    output int assoc_num,
    output int assoc_size,
    output int dyn_size,
    output int queue_size
);
    int dynamic_arr[];
    int queue_arr[$];
    int assoc_arr[int];
    always_comb begin
        dynamic_arr = new[5];
        queue_arr = {1, 2, 3};
        assoc_arr[10] = 100;
        assoc_arr[20] = 200;
        dyn_size = dynamic_arr.size();
        queue_size = queue_arr.size();
        assoc_size = assoc_arr.size();
        assoc_num = assoc_arr.num();
        dynamic_arr = new[0];
        queue_arr = {};
        assoc_arr.delete();
        dyn_size = dynamic_arr.size();
        queue_size = queue_arr.size();
        assoc_size = assoc_arr.size();
        assoc_num = assoc_arr.num();
    end
endmodule

