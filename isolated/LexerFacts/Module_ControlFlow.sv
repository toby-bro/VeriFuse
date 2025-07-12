module Module_ControlFlow (
    input bit clk,
    input logic [7:0] data_in,
    input bit reset_n,
    input logic [2:0] sel_in,
    output reg [7:0] data_out
);
    reg [7:0] temp;
    always_comb begin
        unique case (sel_in)
            3'b000: temp = data_in;
            3'b001: temp = data_in + 1;
            3'b010: temp = data_in - 1;
            default: temp = 8'hAA;
        endcase
    end
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            data_out <= 8'h00;
        else
            data_out <= temp;
    end
endmodule

