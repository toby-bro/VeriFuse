module mod_always_delay (
    input logic clk,
    input logic rst,
    output logic out
);
    always @(posedge clk or negedge rst) begin
    if (!rst) begin
        out <= 1'b0;
    end else begin
        #5 out <= ~out;
    end
    end
endmodule

