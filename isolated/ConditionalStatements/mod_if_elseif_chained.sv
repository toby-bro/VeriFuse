module mod_if_elseif_chained (
    input bit [7:0] in_value,
    output bit [2:0] out_category
);
always_comb begin
    if (in_value < 10) begin
        out_category = 3'd0;
    end else if (in_value < 50) begin
        out_category = 3'd1;
    end else if (in_value < 100) begin
        out_category = 3'd2;
    end else begin
        out_category = 3'd3;
    end
end
endmodule

