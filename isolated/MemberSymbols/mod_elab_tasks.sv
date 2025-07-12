module mod_elab_tasks (
    input logic dummy_in_elab,
    output logic out_status_elab
);
    parameter int VAL_ELAB = 7;
    logic unused;
    assign unused          = VAL_ELAB > 0;
    assign out_status_elab = dummy_in_elab;
    class my_class_elab;
        string status;
        function new(string s);
            status = s;
        endfunction
    endclass
    always_comb begin
        my_class_elab cls;
        cls = new("Elab task module");
    end
endmodule

