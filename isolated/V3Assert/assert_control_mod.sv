module assert_control_mod (
    input logic clk,
    input logic [1:0] trigger,
    output logic ctrl_out
);
    always @(posedge clk) begin
        if (trigger == 2'b01) begin
            $asserton(1, 1);
        end else if (trigger == 2'b10) begin
            $assertoff(2, 2);
        end else if (trigger == 2'b11) begin
            $assertkill(4, 4);
        end
    end
    assign ctrl_out = trigger[0];
endmodule

