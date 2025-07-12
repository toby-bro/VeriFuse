module mod_assign (
    input wire [7:0] data_in_assign,
    input wire in_drive,
    input wire in_val_simple,
    input wire var_in_assign,
    output wire [7:0] data_out_assign,
    output wire drive_out_assign,
    output wire simple_out_assign,
    output wire var_out_assign
);
    wire internal_simple;
    assign internal_simple     = in_val_simple;
    assign simple_out_assign   = internal_simple;
    assign (weak1, weak0) drive_out_assign = in_drive;
    assign (supply0, supply1) data_out_assign = data_in_assign;
    assign var_out_assign = var_in_assign;
    class my_class_assign;
        int count;
        function new();
            count = 0;
        endfunction
    endclass
    always_comb begin
        my_class_assign cls;
        cls = new();
        cls.count = cls.count + 1;
    end
endmodule

