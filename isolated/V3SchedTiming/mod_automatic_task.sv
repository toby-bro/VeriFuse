module mod_automatic_task (
    input int i_val,
    output int o_val
);
    task automatic update_val(input int in_v, output int out_v);
        out_v = in_v * 2;
    endtask
    always_comb begin
        int temp_val;
        update_val(i_val, temp_val);
        o_val = temp_val;
    end
endmodule

