module forwarding_typedef_mod (
    input logic [31:0] in_val
);
    always_comb begin
        out_struct.field1 = in_val[15:0];
        out_struct.field2 = in_val[31:16];
    end
endmodule

