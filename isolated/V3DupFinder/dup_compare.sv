module dup_compare (
    input int val_a,
    input int val_b,
    input int val_c,
    output logic [5:0] indicators
);
    always_comb begin
        indicators = '0;
        indicators[0] = (val_a == val_b);
        indicators[1] = (val_a != val_b);
        indicators[2] = (val_a > val_b);
        indicators[3] = (val_a < val_b);
        indicators[4] = (val_a >= val_b);
        indicators[5] = (val_a <= val_b);
        if (val_b == val_c) begin
            indicators = indicators | 6'b111111;
        end
        if (val_a > val_c) begin
            indicators = indicators & 6'b000000;
        end
        if ((val_a < val_b) && (val_b > val_c)) begin
             indicators[0] = 1;
        end else if ((val_a >= val_b) || (val_b <= val_c)) begin
             indicators[1] = 1;
        end
    end
endmodule

