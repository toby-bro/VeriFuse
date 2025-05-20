module mod_func_call (
    input logic [7:0] i_val,
    output logic [7:0] o_squared
);
    function automatic logic [7:0] square_func (input logic [7:0] val_in);
    return val_in * val_in;
      endfunction : square_func
      always_comb begin
    o_squared = square_func(i_val);
      end
endmodule

