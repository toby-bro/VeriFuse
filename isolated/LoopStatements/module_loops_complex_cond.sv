module module_loops_complex_cond (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic [7:0] in_c,
    output logic [15:0] out_sum
);
    logic [15:0] result_sum;
    always_comb begin
        int i;
        int k;
        result_sum = 16'b0;
        i = 0;
        while ((i < in_a) && ((in_b > 10) || (in_c == 5))) begin
            result_sum += i;
            i++;
            if (i > 20)
                break;
        end
        for (int j = 0; (j < in_b) && ((in_a > 5) || (in_c != 10)); j++) begin
            result_sum += j * 2;
            if (j > 15)
                break;
        end
        k = 0;
        do begin
            result_sum += k * 3;
            k++;
            if (k > 12)
                break;
        end while ((k < in_c) && (in_a != in_b));
    end
    assign out_sum = result_sum;
endmodule

