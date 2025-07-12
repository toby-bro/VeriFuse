class MyClass;
    int data;
    function new(); endfunction
    function MyClass copy();
        MyClass new_obj = new();
        new_obj.data = this.data;
        return new_obj;
    endfunction
endclass

module MiscExpressions_CopyClass (
    input int in_data,
    output int out_copied_data
);
    MyClass original_obj;
    MyClass copied_obj;
    always_comb begin
        if (original_obj == null) begin
            original_obj = new();
        end
        original_obj.data = in_data;
        copied_obj = original_obj.copy(); 
        if (copied_obj != null) begin
            out_copied_data = copied_obj.data;
        end else begin
            out_copied_data = 0;
        end
    end
endmodule

