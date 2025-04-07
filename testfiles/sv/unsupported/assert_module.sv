module assert_module (
    input  logic       clk,
    input  logic       rst_n,
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] out
);
    // Simple operation
    assign out = a + b;
    
    // Assertions
    // Assert that the sum doesn't overflow when MSBs are both 0
    property no_overflow_p;
        @(posedge clk) disable iff (!rst_n)
        (a[7] == 1'b0 && b[7] == 1'b0) |-> (out[7] == 1'b0);
    endproperty
    
    assert property (no_overflow_p) else
        $error("Overflow detected when adding positive numbers");
        
    // Assert a and b are never both at max value
    assert property (@(posedge clk) disable iff (!rst_n)
        !(a == 8'hFF && b == 8'hFF))
    else $error("Both inputs at maximum value");

endmodule
