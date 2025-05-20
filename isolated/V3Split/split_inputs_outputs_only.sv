module split_inputs_outputs_only (
    input logic [7:0] in_val_b_l,
    output logic [8:0] out_val_c_l,
    output logic [7:0] out_val_d_l,
    input logic [7:0] in_val_a_l
);
    always @(*) begin
       out_val_c_l = in_val_a_l + in_val_b_l;
       out_val_d_l = in_val_a_l - in_val_b_l;
    end
endmodule

