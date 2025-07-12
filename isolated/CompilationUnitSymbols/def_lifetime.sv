module def_lifetime (
    input logic clk,
    output logic state_out
);
    static logic initialized_reg = 1'b1;
    always_ff @(posedge clk) begin
        automatic logic [3:0] counter;
        counter = counter + 1;
        state_out <= initialized_reg & counter[0];
    end
endmodule

