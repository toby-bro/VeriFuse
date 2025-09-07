module m_caseeq_demo (
    input wire clk,
    input logic in,
    input wire rst,
    output logic eq,
    output logic neq
);
    logic tri_sig = 1'bz;
    assign eq  = (in === tri_sig); 
    assign neq = (in !== tri_sig); 
endmodule

