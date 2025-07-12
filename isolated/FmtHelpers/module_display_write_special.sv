module module_display_write_special (
    input int in_data,
    input real in_real_data,
    input bit trigger,
    output bit out_done
);
    typedef struct {
        byte f1;
        longint f2;
    } display_struct_t;
    display_struct_t display_struct_var;
    typedef union {
        shortint s;
        int i;
    } display_union_t;
    display_union_t display_union_var;
    always_comb begin
        if (trigger) begin
            display_struct_var = '{f1: 8'h5A, f2: 1234567890};
            display_union_var.s = 16'hABCD;
            $display(in_data);
            $display(in_real_data);
            $display("Direct args: ", in_data, ", ", in_real_data);
            $display("Formatted data: %d, %f", in_data, in_real_data);
            $display("Scope: %m Library/Def: %l");
            $write("Write data: ");
            $write(in_data, " ");
            $write("Formatted write: %h %e", in_data, in_real_data);
            $write("\n"); 
        end
    end
    assign out_done = trigger; 
endmodule

