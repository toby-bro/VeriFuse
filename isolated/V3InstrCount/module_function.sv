module module_function (
    input wire [7:0] in_func_a,
    input wire [7:0] in_func_b,
    output logic [7:0] out_func_result
);
    function automatic [7:0] add_and_subtract;
    input [7:0] val1;
    input [7:0] val2;
    reg [7:0] temp;
    begin
    temp = val1 + val2;
    add_and_subtract = temp - 1;
    end
    endfunction
    always_comb begin
    out_func_result = add_and_subtract(in_func_a, in_func_b);
    end
endmodule

