module ph_conditional (
    input logic [3:0] in_a,
    input logic [3:0] in_b,
    input logic sel1,
    input logic sel2,
    output logic [3:0] out_y
);
    logic [3:0] inc_a = in_a + 4'd1;                 
    logic [3:0] dec_b = in_b - 4'd1;                 

    assign out_y = sel1 ? (sel2 ? in_a : in_b)
        : (sel2 ? inc_a : dec_b);    
endmodule
