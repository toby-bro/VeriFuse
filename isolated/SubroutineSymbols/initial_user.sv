class class_with_initial;
    int value = 0;
    function void set_initial_value();
        value = 50;
    endfunction
    function int get_value(); return value; endfunction
endclass

module initial_user (
    input logic dummy_in,
    output int initial_value_out
);
    class_with_initial inst;
    always_comb begin
        if (inst == null) begin
            inst = new();
            inst.set_initial_value();
        end
        initial_value_out = inst.get_value();
    end
endmodule

