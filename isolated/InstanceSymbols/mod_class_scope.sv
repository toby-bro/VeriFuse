module mod_class_scope (
    input logic cs_in,
    output logic cs_out
);
    class my_class;
        int data;
        function new(int val);
            data = val;
        endfunction
    endclass
    my_class my_obj;
    logic dummy_signal = 0;
    always_ff @(posedge dummy_signal) begin : proc_block_for_class
        my_obj = new(10);
        cs_out = cs_in;
    end
    final begin : final_block_for_class
        my_class another_obj;
        another_obj = new(20);
    end
endmodule

