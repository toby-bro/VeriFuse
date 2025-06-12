module function_call_op (
    input logic [7:0] in2,
    output logic [7:0] out,
    input logic [7:0] in1
);
    function automatic logic [7:0] add_values (input logic [7:0] val1, input logic [7:0] val2);
        return val1 + val2;
    endfunction
    assign out = add_values(in1, in2);
endmodule

