module mod_case_standard (
    input bit [7:0] in_cmd,
    output bit [3:0] out_status
);
always_comb begin
    case (in_cmd)
        8'd0, 8'd1, 8'd2: begin
            out_status = 4'hA;
        end
        8'd3, 8'd4: begin
            out_status = 4'hB;
        end
        default: begin
            out_status = 4'hF;
        end
    endcase
end
endmodule

