class ParamClass #(
    parameter int SIZE = 8
);
        logic [SIZE-1:0] data_array;
        int param_member;
        function new(logic [SIZE-1:0] arr, int pm);
            data_array = arr;
            param_member = pm;
        endfunction
endclass

module ModuleWithParamClass (
    input int data_val,
    output int param_sum_out
);
    ParamClass #(16) param_instance_16;
    always_comb begin
        logic [15:0] temp_array_16;
        temp_array_16 = $unsigned(data_val);
        param_instance_16 = new(temp_array_16, data_val + 5);
        param_sum_out = param_instance_16.param_member + $unsigned(param_instance_16.data_array[0]);
    end
endmodule

