module func_user_defined (
    input logic [15:0] data_in1,
    input logic [15:0] data_in2,
    output logic [15:0] data_out
);
    function automatic [15:0] complex_op(input [15:0] d1, input [15:0] d2);
        logic [15:0] temp_func_res;
        temp_func_res = (d1 & d2) | (d1 ^ d2);
        return temp_func_res + d2;
    endfunction
    assign data_out = complex_op(data_in1, data_in2);
endmodule

