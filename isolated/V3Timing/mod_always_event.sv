module mod_always_event (
    output logic out,
    input logic clk,
    input logic rst,
    input logic in
);
    always @(posedge clk or negedge rst) begin
    if (!rst) begin
        out <= 1'b0;
    end else begin
        out <= in;
    end
    end
endmodule

