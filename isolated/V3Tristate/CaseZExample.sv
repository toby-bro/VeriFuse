module CaseZExample (
    input wire [1:0] sel,
    input wire [3:0] data_in,
    output reg [3:0] case_out
);
    wire [3:0] local_data;
    assign local_data = data_in;
    always @* begin
        casez (sel)
            2'b0?: case_out = local_data;
            2'b10: case_out = 4'b1111;
            default: case_out = 4'b0000;
        endcase
    end
endmodule

