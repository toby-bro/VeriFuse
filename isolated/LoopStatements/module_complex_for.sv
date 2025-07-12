module module_complex_for (
    input logic [7:0] in_end,
    input logic [7:0] in_start,
    output logic [15:0] out_accum
);
    logic [15:0] accumulator;
    always_comb begin
        accumulator = 16'b0;
        for (int i = in_start, j = in_end; i < j; i = i + 1, j = j - 1) begin
            if (i < (j >> 1))
                accumulator = accumulator + i;
            else
                accumulator = accumulator - j;
            if ((i % 2) == 0)
                accumulator = accumulator + 1;
            else
                accumulator = accumulator - 1;
        end
    end
    assign out_accum = accumulator;
endmodule

