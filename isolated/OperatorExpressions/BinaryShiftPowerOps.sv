module BinaryShiftPowerOps (
    input int exp_pow,
    input int exp_val,
    input logic [3:0] sh,
    input logic [7:0] val,
    output int out_power,
    output logic [7:0] out_sal,
    output logic [7:0] out_sar,
    output logic [7:0] out_sll,
    output logic [7:0] out_srl
);
    assign out_sll   = val <<  sh;
    assign out_srl   = val >>  sh;
    assign out_sal   = val <<< sh;
    assign out_sar   = val >>> sh;
    assign out_power = exp_val ** exp_pow;
endmodule

