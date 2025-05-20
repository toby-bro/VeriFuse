module mod_func_caller (
    input logic func_in,
    output logic func_out
);
    initial begin
        func_out = func_caller(func_in);
    end
endmodule

