module ref_arg_automatic_context (
    input int data_in,
    output int data_out_ref
);
    int internal_data = 0;
    task automatic update_data_ref(ref int data, input int add);
        data = data + add;
    endtask
    always_comb begin
        update_data_ref(internal_data, data_in);
        data_out_ref = internal_data;
    end
endmodule

