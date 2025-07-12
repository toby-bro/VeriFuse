module mod_case_inside_range (
    input int in_level,
    output bit [1:0] out_level_cat
);
always_comb begin
    case (in_level) inside
        [1:10]: begin
            out_level_cat = 2'b00;
        end
        [11:50], [100:200]: begin
            out_level_cat = 2'b01;
        end
        default: begin
            out_level_cat = 2'b11;
        end
    endcase
end
endmodule

