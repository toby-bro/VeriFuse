module mod_casex_wildcard_overlap_priority (
    input bit [3:0] in_mask_x,
    output bit [1:0] out_match_type_x
);
always_comb begin
    out_match_type_x = 2'b01;
    priority casex (in_mask_x)
        4'b1X0Z: begin
            out_match_type_x = 2'b10;
        end
        4'b10?Z: begin
            out_match_type_x = 2'b11;
        end
        4'bZ1?X: begin
            out_match_type_x = 2'b00;
        end
        default: begin
            out_match_type_x = 2'b01;
        end
    endcase
end
endmodule

