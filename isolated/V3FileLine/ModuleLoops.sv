module ModuleLoops (
    input integer in1,
    input integer in2,
    output integer out1,
    output integer out2
);
    integer i;
    integer temp_sum = 0;
    integer temp_prod = 1;
    always_comb begin
        temp_sum = 0;
        for (i = 0; i < 5; i = i + 1) begin
            temp_sum = temp_sum + (in1 + i);
        end
        out1 = temp_sum;
        temp_prod = 1;
        i = 1;
        while (i <= in2 && i < 8) begin
            temp_prod = temp_prod * i;
            i = i + 1;
        end
        out2 = temp_prod;
    end
endmodule

