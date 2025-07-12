module member_access_class (
    input int in_val,
    output bit is_null,
    output int out_field,
    output int out_method_result
);
    class MyClass;
        int field = 10; 
        function int get_field(); 
            return field;
        endfunction
        function int get_field_from_this(); 
            return this.field; 
        endfunction
    endclass
    MyClass obj; 
    initial begin : instantiate_class 
        obj = new(); 
    end
    always_comb begin
        is_null = (obj == null); 
        if (obj != null) begin
            out_field = obj.field;
            out_method_result = obj.get_field();
        end else begin
            out_field = 0;
            out_method_result = 0;
        end
    end
endmodule

