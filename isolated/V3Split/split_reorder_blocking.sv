module split_reorder_blocking (
    input logic [7:0] in_a_g,
    input logic [7:0] in_b_g,
    output logic [7:0] out_p_g,
    output logic [7:0] out_q_g
);
    logic [7:0] mid_x_g;
    logic [7:0] mid_y_g;
    always @(*) begin
        mid_x_g = in_a_g * 2;
        mid_y_g = mid_x_g + in_b_g;
        out_p_g = mid_y_g - 1;
        out_q_g = mid_x_g / 2;
    end
endmodule

