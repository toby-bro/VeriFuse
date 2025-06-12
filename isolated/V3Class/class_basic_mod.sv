module class_basic_mod (
    input int input_val,
    output int output_val
);
    class BasicClass;
        int data;
        function new(int val);
            data = val;
        endfunction
        function int get_data();
            return data;
        endfunction
    endclass
    BasicClass inst;
    int temp_data;
    always_comb begin
        inst = new(input_val);
        temp_data = inst.get_data();
    end
    assign output_val = temp_data;
endmodule

