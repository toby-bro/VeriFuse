class SimpleClass;
    int m_val = 10;
    function int get_val();
        return m_val;
    endfunction
endclass

module mod_class_inst (
    input logic dummy_in,
    output int data_out_class
);
    always_comb begin
        SimpleClass inst = new();
        data_out_class = inst.get_val();
    end
endmodule

