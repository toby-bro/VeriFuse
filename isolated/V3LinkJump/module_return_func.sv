module module_return_func (
    input logic [7:0] in_val,
    output logic [7:0] out_res
);
    function automatic logic [7:0] my_func (input logic [7:0] value);
        logic [7:0] temp;
        temp = value * 2;
        if (temp > 50) begin
            return 8'hFF;
        end
        return temp;
    endfunction
    always_comb begin: func_call_block
        out_res = my_func(in_val);
    end
endmodule

