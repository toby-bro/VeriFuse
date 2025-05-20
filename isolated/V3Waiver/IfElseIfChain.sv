module IfElseIfChain (
    input logic [7:0] data2,
    input logic [7:0] data3,
    output logic [7:0] selected_data,
    input logic [1:0] sel_code,
    input logic [7:0] data0,
    input logic [7:0] data1
);
    always_comb begin
        if (sel_code == 2'b00) begin
            selected_data = data0;
        end else if (sel_code == 2'b01) begin
            selected_data = data1;
        end else if (sel_code == 2'b10) begin
            selected_data = data2;
        end else begin
            selected_data = data3;
        end
    end
endmodule

