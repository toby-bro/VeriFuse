class MySimpleClass;
    int data;
    function new(int val);
        data = val;
    endfunction
    function int getData();
        return data;
    endfunction
endclass

module Class_Usage (
    input wire trigger_in,
    output reg status_out
);
    function automatic int instantiate_and_use_class(input int val);
        MySimpleClass obj = new(val);
        return obj.getData();
    endfunction
    always_comb begin
        int temp_val;
        if (trigger_in) begin
            temp_val = instantiate_and_use_class(100);
        end else begin
            temp_val = instantiate_and_use_class(200);
        end
        status_out = (temp_val == 100) || (temp_val == 200);
    end
endmodule

