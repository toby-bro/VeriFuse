module macro_concat_user (
    input logic [3:0] concat_in,
    output logic [7:0] concat_out
);
    `define MAKE_NAME(a,b) a``b
    logic var_signal;
    always_comb begin
        `MAKE_NAME(var,_signal) = concat_in[0];
    end
    assign concat_out = {4'b0, concat_in[3:1], var_signal};
endmodule

