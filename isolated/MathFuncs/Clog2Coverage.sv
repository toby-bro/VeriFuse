module Clog2Coverage (
    input int data_in,
    output int clog2_out
);
always @(*) begin
    clog2_out = $clog2(data_in);
end
endmodule

