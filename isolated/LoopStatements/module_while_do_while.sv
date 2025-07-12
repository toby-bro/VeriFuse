module module_while_do_while (
    input logic [3:0] in_count,
    output logic [7:0] out_result
);
    logic [7:0] temp_res;
    logic [3:0] counter_w;
    logic [3:0] counter_dw;
    always_comb begin
        temp_res  = 8'b0;
        counter_w = in_count;
        while (counter_w > 0) begin
            temp_res = temp_res + 1;
            counter_w = counter_w - 1;
        end
        counter_dw = (in_count == 0) ? 1 : in_count;
        do begin
            temp_res = temp_res + 2;
            counter_dw = counter_dw - 1;
        end while (counter_dw > 0 && counter_dw < 10);
    end
    assign out_result = temp_res;
endmodule

