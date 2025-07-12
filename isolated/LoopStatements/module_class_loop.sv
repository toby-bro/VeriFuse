module module_class_loop (
    input int in_initial_val,
    input int in_loop_count,
    output int out_class_sum
);
    class Adder;
        int value;
        function new(int initial_val);
            value = initial_val;
        endfunction
        function int add(int val);
            value += val;
            return value;
        endfunction
    endclass
    int total;
    always_comb begin
        Adder my_adder;
        total = 0;
        if (in_loop_count > 0 && in_loop_count < 10) begin
            my_adder = new(in_initial_val);
            for (int i = 0; i < in_loop_count; i++) begin
                total = my_adder.add(i);
            end
        end
        else
            total = in_initial_val;
    end
    assign out_class_sum = total;
endmodule

