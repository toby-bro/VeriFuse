module range_select_indexed_packed (
    input logic [31:0] in_vec,
    input int start_index,
    input int width,
    output logic [7:0] out_down,
    output logic [7:0] out_up
);
    always_comb begin
        if (start_index >= 0 && width > 0 && start_index + width <= 32) begin
            case (width)
                1: out_up = in_vec[start_index +: 1];
                2: out_up = in_vec[start_index +: 2];
                4: out_up = in_vec[start_index +: 4];
                8: out_up = in_vec[start_index +: 8];
                default: out_up = 'x;
            endcase
        end else begin
            out_up = 'x;
        end
        if (start_index >= width - 1 && width > 0 && start_index < 32) begin
            case (width)
                1: out_down = in_vec[start_index -: 1];
                2: out_down = in_vec[start_index -: 2];
                4: out_down = in_vec[start_index -: 4];
                8: out_down = in_vec[start_index -: 8];
                default: out_down = 'x;
            endcase
        end else begin
            out_down = 'x;
        end
    end
endmodule

