module mod_generate_if (
    input logic i_select,
    input logic i_a,
    input logic i_b,
    output logic o_mux_out
);
    logic internal_common;
      generate
    if (1) begin : gen_true
      logic internal_true;
      always_comb begin
        internal_true = i_a;
        o_mux_out = internal_true;
        internal_common = 1'b1;
      end
    end else begin : gen_false
      logic internal_false;
    end
      endgenerate
      always_comb begin
     internal_common = internal_common ^ i_select;
      end
endmodule

