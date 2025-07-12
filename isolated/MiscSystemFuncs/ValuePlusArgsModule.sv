module ValuePlusArgsModule (
    input bit enable_args_check,
    output int plusarg_int_val,
    output real plusarg_real_val,
    output bit plusarg_success_int,
    output bit plusarg_success_real
);
int temp_int;
real temp_real;
always_comb begin
    if (enable_args_check) begin
        plusarg_success_int = $value$plusargs("my_int_arg=%d", temp_int);
        plusarg_success_real = $value$plusargs("my_real_arg=%f", temp_real);
    end else begin
        temp_int = 0;
        temp_real = 0.0;
        plusarg_success_int = 0;
        plusarg_success_real = 0;
    end
    plusarg_int_val = temp_int;
    plusarg_real_val = temp_real;
end
endmodule

