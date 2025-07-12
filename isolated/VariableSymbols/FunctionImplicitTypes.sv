module FunctionImplicitTypes (
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] implicit_result_var;
    always_comb begin
        data_out = add_implicit(data_in, 8'h03, implicit_result_var);
    end
    function logic [7:0] add_implicit(
        input  logic [7:0] data_a,
        input  logic [7:0] data_b,
        output logic [7:0] result
    );
        result = data_a + data_b;
        return result;
    endfunction
endmodule

