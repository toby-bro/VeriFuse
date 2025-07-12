module mod_case_matches_pattern (
    input bit [7:0] in_threshold,
    output bit [1:0] out_pattern_match_type
);
always_comb begin
    out_pattern_match_type = 2'b11;
    if (in_packet.id == 4'hA) begin
        out_pattern_match_type = 2'b00;
    end else if (in_packet.id == 4'hB && in_packet.data > in_threshold) begin
        out_pattern_match_type = 2'b01;
    end else if (in_packet.id == 4'hC && in_packet.data == 8'd5) begin 
        out_pattern_match_type = 2'b10;
    end else begin
        out_pattern_match_type = 2'b11;
    end
end
endmodule

