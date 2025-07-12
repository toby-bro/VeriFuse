module module_integral_float_formats (
    input bit [7:0] in_byte,
    input int in_int,
    input real in_real,
    output bit out_status,
    output string s_float,
    output string s_integral,
    output string s_mixed
);
    localparam int param_int = 42;
    localparam byte param_byte = 8'hAB;
    localparam real param_real = 3.14;
    bit status = 1'b1;
    always_comb begin
        s_integral = $sformatf("Param: %d %h %o %b %x %c", param_int, param_int, param_int, param_byte, param_byte, param_byte);
        s_integral = {s_integral, $sformatf("Input: %d %h %o %b %x %c", in_int, in_int, in_int, in_byte, in_byte, in_byte)};
    end
    always_comb begin
        s_float = $sformatf("Param Real: %e %f %g %t", param_real, param_real, param_real, param_real);
        s_float = {s_float, $sformatf("Input Real: %e %f %g %t", in_real, in_real, in_real, in_real)};
    end
    always_comb begin
        s_mixed = $sformatf("Mixed: %d %f %h %e", in_int, in_real, in_byte, param_real);
    end
    assign out_status = status;
endmodule

