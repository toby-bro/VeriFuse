class MyClass;
    int data;
    function new(); endfunction
    function MyClass copy();
        MyClass new_obj = new();
        new_obj.data = this.data;
        return new_obj;
    endfunction
endclass

module MiscExpressions_CopyClassNewCopy (
    input int in_data,
    output int out_copied_data
);
    MyClass copied_obj;
    always_comb begin
        copied_obj = new(); 
        if (copied_obj != null) begin
            copied_obj.data = in_data;
            out_copied_data = copied_obj.data;
        end else begin
            out_copied_data = 0;
        end
    end
endmodule

