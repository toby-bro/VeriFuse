module m_caseeq_demo (
    input logic in,
    output logic eq,
    output logic neq
);
    logic tri_sig = 1'bz;
    assign eq  = (in === tri_sig); 
    assign neq = (in !== tri_sig); 
endmodule

module top;
    logic in;
    logic eq;
    logic neq;
    m_caseeq_demo dut (
        .in(in),
        .eq(eq),
        .neq(neq)
    );

    initial begin
        in = 0; 

        #10; 

        $display("eq = %b", eq);
        $display("neq = %b", neq);

        $finish;
    end
endmodule

