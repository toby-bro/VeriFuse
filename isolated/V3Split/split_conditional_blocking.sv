module split_conditional_blocking (
    output logic [7:0] out_val_o,
    input logic condition_o,
    input logic [7:0] in_true_o,
    input logic [7:0] in_false_o
);
    always @(*) begin
        if (condition_o) begin
            out_val_o = in_true_o;
        end else begin
            out_val_o = in_false_o;
        end
    end
endmodule

