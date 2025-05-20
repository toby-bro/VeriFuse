module dup_nested_if (
    input logic [2:0] mode,
    input logic [7:0] val1,
    input logic [7:0] val2,
    output logic [7:0] res
);
    always_comb begin
        res = '0;
        if (mode == 3'b001) begin
            if (val1 > val2) begin
                res = val1 + val2;
            end else begin
                res = val1 - val2;
            end
        end else if (mode == 3'b010) begin
            if (val1 > val2) begin
                res = val1 + val2;
            end else begin
                res = val1 - val2;
            end
        end else if (mode == 3'b011) begin
            if (val1 < val2) begin
                res = val1 * val2;
            end else begin
                res = val1 / ((val2 == 0) ? 1 : val2);
            end
        end else if (mode == 3'b100) begin
             if (val1 != val2) begin
                if (val1 > val2) res = val1;
                else res = val2;
             end else begin
                res = val1 + val2;
             end
        end
        else begin
            res = val1 ^ val2;
        end
    end
endmodule

