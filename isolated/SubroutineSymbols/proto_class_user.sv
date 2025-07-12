class class_with_proto;
    int data;
    function new(int initial_data); data = initial_data; endfunction
    function int process_internal(input int val);
        return data * val;
    endfunction
endclass

module proto_class_user (
    input int factor,
    input int in_data,
    output int out_result
);
    class_with_proto inst;
    always_comb begin
        if (inst == null) inst = new(in_data);
        out_result = inst.process_internal(factor);
    end
endmodule

