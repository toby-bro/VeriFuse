module func_task_typedef (
    output logic [15:0] val_out,
    input logic [15:0] val_in,
    input logic enable
);
    typedef logic [15:0] my_data_t;
    my_data_t temp_val;
    function automatic my_data_t add_one(my_data_t input_val);
        return input_val + 1;
    endfunction
    task automatic set_value(my_data_t set_val);
        temp_val = set_val;
    endtask
    always_comb begin
        if (enable) begin
            set_value(add_one(val_in));
        end else begin
            set_value(val_in);
        end
        val_out = temp_val;
    end
endmodule

