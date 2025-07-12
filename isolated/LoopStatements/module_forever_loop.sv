module module_forever_loop (
    input logic clk,
    input logic reset_n,
    output logic toggle_out
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            toggle_out <= 1'b0;
        else
            forever begin
                toggle_out <= ~toggle_out;
                break;
            end
    end
endmodule

