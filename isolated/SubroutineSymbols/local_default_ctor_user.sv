class base_with_local_default_ctor;
    local int local_const = 100;
    int data;
    function new(input int initial_data = 100); 
        data = initial_data;
    endfunction
    function int get_data(); return data; endfunction
endclass

class derived_inheriting_local_default extends base_with_local_default_ctor;
    function new();
        super.new(); 
    endfunction
endclass

module local_default_ctor_user (
    input logic dummy_in,
    output int derived_data_out
);
    derived_inheriting_local_default inst;
    always_comb begin
        if (inst == null) begin
            inst = new();
        end
        derived_data_out = inst.get_data();
    end
endmodule

