module function_module (
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic       select,
    output logic [7:0] result
);
    // Module with function
    function logic [7:0] max_func(logic [7:0] x, logic [7:0] y);
        return (x > y) ? x : y;
    endfunction

    function logic [7:0] min_func(logic [7:0] x, logic [7:0] y);
        return (x < y) ? x : y;
    endfunction

    // Use function based on select
    assign result = select ? max_func(a, b) : min_func(a, b);
endmodule
