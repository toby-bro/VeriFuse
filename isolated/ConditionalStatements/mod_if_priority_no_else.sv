module mod_if_priority_no_else (
    input bit [1:0] in_sel,
    output bit out_priority
);
always_comb begin
    out_priority = 1'b0;
    priority if (in_sel == 2'b00) begin
        out_priority = 1'b1;
    end else if (in_sel == 2'b01) begin
        out_priority = 1'b0;
    end
end
endmodule

