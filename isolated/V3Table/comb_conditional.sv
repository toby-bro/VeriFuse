module comb_conditional (
    input bit [7:0] data1,
    input bit [7:0] data2,
    input bit sel,
    output bit [7:0] result1,
    output bit [7:0] result2
);
    always @* begin
        if (sel) begin
            result1 = data1;
            result2 = data1;
        end else begin
            result1 = data2;
            result2 = data2;
        end
    end
endmodule

