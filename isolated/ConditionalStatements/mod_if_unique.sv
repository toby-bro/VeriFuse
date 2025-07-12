module mod_if_unique (
    input bit [1:0] in_sel,
    output bit out_unique
);
always_comb begin
    unique if (in_sel == 2'b00) begin
        out_unique = 1'b1;
    end else if (in_sel == 2'b01) begin
        out_unique = 1'b0;
    end else begin
        out_unique = 1'b1;
    end
end
endmodule

