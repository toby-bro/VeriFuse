module module_latch (
    output reg [7:0] out_latch_reg,
    input wire [7:0] in_latch_data,
    input wire in_latch_en
);
    always_latch begin
    if (in_latch_en) begin
        out_latch_reg = in_latch_data;
    end
    end
endmodule

