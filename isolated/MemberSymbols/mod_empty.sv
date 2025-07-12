module mod_empty (
    input logic in1,
    output logic out1
);
    logic temp_empty;
    assign temp_empty = in1;
    assign out1 = temp_empty;
    class my_class_empty;
        int val;
        function new(int v);
            val = v;
        endfunction
    endclass
    always_comb begin
        my_class_empty cls;
        cls = new(1);
    end
endmodule

