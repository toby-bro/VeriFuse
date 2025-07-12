module m_class_methods (
    input int initial_val,
    output int instance_result,
    output int new_instance_result,
    output int static_result
);
    class MyClass;
        int instance_var;
        static function automatic int static_method(input int val);
            return val * 2;
        endfunction
        function automatic int instance_method(input int val);
            this.instance_var = val;
            return this.instance_var + 1;
        endfunction
        function new(input int val);
            instance_var = val;
        endfunction
    endclass
    MyClass instance1;
    MyClass instance2;
    initial begin
        static_result = MyClass::static_method(initial_val);
        instance1 = new(initial_val + 1);
        instance_result = instance1.instance_method(initial_val + 5);
        instance2 = new(initial_val + 10);
        new_instance_result = instance2.instance_method(initial_val + 15);
    end
endmodule

