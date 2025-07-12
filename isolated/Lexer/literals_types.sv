module literals_types (
    input logic [7:0] in_val,
    output logic [15:0] out_val
);
    logic [7:0]  byte_lit;
    logic [15:0] word_lit;
    real         r_val;
    time         t_val;
    always_comb begin
        byte_lit = '0;
        byte_lit = 8'b1010_1100;
        word_lit = 16'hDEAD;
        r_val    = 3.14e2;
        t_val    = 10ns;
        out_val  = {byte_lit, word_lit[7:0]};
        if (in_val inside {8'h00, 8'hFF, [8'h10:8'h20]})
            out_val = 16'h1234;
    end
endmodule

