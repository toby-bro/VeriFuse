module mod_if_else_simple (
    input bit [3:0] in_data,
    output bit [3:0] out_result
);
always_comb begin
    if (in_data > 8) begin
        out_result = in_data + 1;
    end else begin
        out_result = in_data - 1;
    end
end
endmodule

