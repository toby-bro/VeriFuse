module ClassCounter (
    input logic clk,
    output logic [7:0] count_out
);
    class Counter;
        int count;
        function void inc(); count++; endfunction
    endclass
    Counter c;
    always_ff @(posedge clk) begin
        if (c == null) c = new();
        c.inc();
        count_out <= c.count[7:0];
    end
endmodule

