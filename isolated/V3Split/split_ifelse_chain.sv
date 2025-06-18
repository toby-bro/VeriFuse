module split_ifelse_chain (
    input logic c1_x,
    input logic c2_x,
    input logic c3_x,
    input logic clk_x,
    input logic [7:0] v1_x,
    input logic [7:0] v2_x,
    input logic [7:0] v3_x,
    input logic [7:0] v4_x,
    output logic [7:0] out_x
);
    always @(posedge clk_x) begin
        if (c1_x) begin
            out_x <= v1_x;
        end else if (c2_x) begin
            out_x <= v2_x;
        end else if (c3_x) begin
            out_x <= v3_x;
        end else begin
            out_x <= v4_x;
        end
    end
endmodule

