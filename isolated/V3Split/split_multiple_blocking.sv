module split_multiple_blocking (
    output logic [3:0] data_out2_n,
    input logic [3:0] data_in_n,
    output logic [3:0] data_out1_n
);
    logic [3:0] temp_n;
    always @(*) begin
        temp_n = data_in_n + 1;
        data_out1_n = temp_n * 2;
        data_out2_n = temp_n + 3;
    end
endmodule

