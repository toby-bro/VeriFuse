module LogicDependencyChain (
    output logic q_out,
    input logic d_in,
    input logic clk
);
    logic q1, q2;
    always @(posedge clk) begin
        q1 <= d_in;
    end
    always @(q1) begin
        q2 = ~q1;
    end
    assign q_out = q2;
endmodule

