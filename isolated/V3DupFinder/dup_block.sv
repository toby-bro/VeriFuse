module dup_block (
    val_b,
    input logic mode,
    output logic [7:0] out_res,
    input logic [7:0] val_a
);
    logic [7:0] inter_res1;
    logic [7:0] inter_res2;
    logic [7:0] inter_res3;
    assign inter_res1 = val_a + val_b;
    always_comb begin
        inter_res2 = val_a - val_b;
        if (mode) begin
            out_res = inter_res2 * 2;
        end else begin
            out_res = inter_res2 / 2;
        end
        inter_res3 = val_a - val_b;
            if (!mode) begin
                out_res = out_res + (inter_res3 / 2);
        end else begin
            out_res = out_res + (inter_res3 * 2);
        end
        out_res = out_res + inter_res1;
        begin : repeated_block
            logic [7:0] temp_val = val_a & val_b;
            if (mode) out_res = out_res | temp_val;
            else out_res = out_res & temp_val;
        end
            begin : another_repeated_block
                logic [7:0] temp_val = val_a & val_b;
                if (mode) out_res = out_res | temp_val;
                else out_res = out_res & temp_val;
        end
    end
endmodule

