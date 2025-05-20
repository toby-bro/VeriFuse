module split_combo_nb (
    output logic [7:0] x_bb,
    output logic [7:0] y_bb,
    output logic [7:0] z_bb,
    input logic clk_bb,
    input logic [7:0] a_bb,
    input logic [7:0] b_bb,
    input logic [7:0] c_bb
);
    logic [7:0] temp_bb;
    always @(posedge clk_bb) begin
        x_bb <= a_bb + b_bb;
        y_bb <= x_bb - c_bb;
        z_bb <= a_bb * c_bb;
    end
endmodule

