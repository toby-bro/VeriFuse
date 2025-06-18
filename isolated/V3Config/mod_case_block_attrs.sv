module mod_case_block_attrs (
    input wire [1:0] i_sel,
    input wire [3:0] i_val,
    output logic [3:0] o_out
);
    logic [3:0] l_temp;
    always_comb begin
        (* full_case *)
        (* parallel_case *)
        case (i_sel)
            2'b00: l_temp = i_val;
            2'b01: l_temp = i_val << 1;
            2'b10: l_temp = i_val >> 1;
            default: l_temp = 4'bxxxx;
        endcase
        (* coverage_off *)
        begin : my_named_block
            o_out = l_temp;
        end
    end
endmodule

