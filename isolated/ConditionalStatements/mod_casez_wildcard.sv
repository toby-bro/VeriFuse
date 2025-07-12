module mod_casez_wildcard (
    input bit [3:0] in_mask_z,
    output bit [1:0] out_match_type_z
);
always_comb begin
    casez (in_mask_z)
        4'b10?0: begin
            out_match_type_z = 2'b00;
        end
        4'b011?: begin
            out_match_type_z = 2'b01;
        end
        default: begin
            out_match_type_z = 2'b11;
        end
    endcase
end
endmodule

