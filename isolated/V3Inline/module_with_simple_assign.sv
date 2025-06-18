module module_with_simple_assign (
    input logic [1:0] state_in,
    output logic cover_hit,
    input logic clk,
    input logic reset
);
    logic [1:0] current_state;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            current_state <= 2'b00;
        end else begin
            current_state <= state_in;
        end
    end
    assign cover_hit = (current_state inside {2'b00, 2'b11});
endmodule

