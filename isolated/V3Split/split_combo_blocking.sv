module split_combo_blocking (
    input logic [7:0] b_aa,
    input logic [7:0] c_aa,
    output logic [7:0] x_aa,
    output logic [7:0] y_aa,
    output logic [7:0] z_aa,
    input logic [7:0] a_aa
);
    logic [7:0] temp_aa;
    always @(*) begin
        x_aa = a_aa + b_aa;
        y_aa = x_aa - c_aa;
        z_aa = a_aa * c_aa;
    end
endmodule

