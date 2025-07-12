module SimpleLogicTest (
    input bit [7:0] data_in,
    input bit select_signal,
    output bit [7:0] data_out
);
    logic [7:0] temp_data;
    always_comb begin
        if (select_signal) begin
            temp_data = data_in + 1;
        end else begin
            temp_data = data_in - 1;
        end
        data_out = temp_data;
    end
endmodule

