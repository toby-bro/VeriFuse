module mod_class_inst (
    input logic i_data_in,
    input logic i_enable,
    output logic o_data_out
);
    class MyClass;
        logic my_member;
        function new();
            my_member = 1'b0;
        endfunction
        function void set_member(logic val);
            my_member = val;
        endfunction : set_member
        function logic get_member();
            return my_member;
        endfunction : get_member
    endclass
    MyClass my_object_handle;
    function automatic logic process_with_class(input logic enable_in, input logic data_in);
        logic result;
        if (enable_in) begin
            my_object_handle = new();
            my_object_handle.set_member(data_in);
            result = my_object_handle.get_member();
        end else begin
            my_object_handle = null;
            result = 1'b0;
        end
        return result;
    endfunction : process_with_class
    always_comb begin
        o_data_out = process_with_class(i_enable, i_data_in);
    end
endmodule

