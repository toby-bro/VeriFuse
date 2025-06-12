module simple_for_loop (
    input logic [7:0] in_data,
    output logic [7:0] out_sum
);
    logic [7:0] sum;
    always_comb begin
        sum = 8'h00;
        for (int i = 0; i < 5; i = i + 1) begin
            sum = sum + in_data;
        end
        out_sum = sum;
    end
endmodule

