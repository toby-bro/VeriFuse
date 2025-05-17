typedef enum { STATE_A, STATE_B, STATE_C = 5, STATE_D } my_enum_t;
typedef enum { STATE_A_INC, STATE_B_INC, STATE_C_INC = 5, STATE_D_INC } my_enum_incomplete_t;
module case_basic (
    input [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b00: out_res = 1'b0;
            2'b01: out_res = 1'b1;
            2'b10: out_res = 1'b0;
            2'b11: out_res = 1'b1;
        endcase
    end
endmodule
module casez_xz (
    input [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            3'b1??: out_res = 1'b1;
            3'b0z?: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule
module casez_xz_alt (
    input [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            3'b1?z: out_res = 1'b1;
            3'b0z?: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule
module case_default (
    input [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b01: out_res = 1'b1;
            2'b10: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule
module case_single_default_after_item (
    input [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b01: out_res = 1'b1;
            default: out_res = 1'b0;
            2'b10: out_res = 1'b1;
        endcase
    end
endmodule
/* verilator lint_off CASEOVERLAP */
module casez_overlap (
    input [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            2'b00: out_res = 1'b0;
            2'b01: out_res = 1'b0;
            2'b0?: out_res = 1'b1;
            2'b1?: out_res = 1'b1;
            default: out_res = 1'b0;
        endcase
    end
endmodule
/* verilator lint_on CASEOVERLAP */
module case_priority_unique (
    input [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        (* priority *) (* unique *) case (in_val)
            2'b00: out_res = 1'b0;
            2'b01: out_res = 1'b1;
            2'b10: out_res = 1'b0;
            2'b11: out_res = 1'b1;
        endcase
    end
endmodule
module case_large_width (
    input [20:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            21'd100000: out_res = 1'b1;
            21'd200000: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule
module case_large_width_many_items (
    input [20:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            21'd0: out_res = 1'b0;
            21'd1: out_res = 1'b1;
            21'd2: out_res = 1'b0;
            21'd3: out_res = 1'b1;
            21'd4: out_res = 1'b0;
            21'd5: out_res = 1'b1;
            21'd6: out_res = 1'b0;
            21'd7: out_res = 1'b1;
            21'd8: out_res = 1'b0;
            21'd9: out_res = 1'b1;
            21'd10: out_res = 1'b0;
            21'd11: out_res = 1'b1;
            21'd12: out_res = 1'b0;
            21'd13: out_res = 1'b1;
            21'd14: out_res = 1'b0;
            21'd15: out_res = 1'b1;
            21'd100000: out_res = 1'b1;
            21'd200000: out_res = 1'b0;
            21'd300000: out_res = 1'b1;
            21'd400000: out_res = 1'b0;
            21'd500000: out_res = 1'b1;
            21'd600000: out_res = 1'b0;
            default: out_res = 1'b0;
        endcase
    end
endmodule
module case_enum (
    input my_enum_t in_state,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_state)
            STATE_A: out_res = 1'b1;
            STATE_B: out_res = 1'b0;
            STATE_C: out_res = 1'b1;
            STATE_D: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule
module case_enum_complete_unique (
    input my_enum_t in_state,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        (* unique *) case (in_state)
            STATE_A: out_res = 1'b1;
            STATE_B: out_res = 1'b0;
            STATE_C: out_res = 1'b1;
            STATE_D: out_res = 1'b0;
            default: out_res = 1'b0;
        endcase
    end
endmodule
module case_inside (
    input [3:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val) inside
            4'b0001, 4'b0010: out_res = 1'b1;
            4'b0100: out_res = 1'b0;
            [4'h8:4'hF]: out_res = 1'b1;
            4'b10?z: out_res = 1'b0;
            default: out_res = 1'b0;
        endcase
    end
endmodule
module case_inside_range (
    input [3:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val) inside
            [4'b0000 : 4'b0011]: out_res = 1'b1;
            [4'b0100 : 4'b0111]: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule
module casez_xz_plain (
    input [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            2'b0?: out_res = 1'b1;
            2'b1z: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule
module case_always_ff (
    input clk,
    input rst,
    input [1:0] in_val,
    output reg out_res
);
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            out_res <= 1'b0;
        end else begin
            case (in_val)
                2'b00: out_res <= 1'b0;
                2'b01: out_res <= 1'b1;
                default: out_res <= out_res;
            endcase
        end
    end
endmodule
module case_always_comb (
    input [1:0] in_val,
    output reg out_res
);
    always_comb begin
        case (in_val)
            2'b00: out_res = 1'b0;
            2'b01: out_res = 1'b1;
            2'b10: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule
/* verilator lint_off CASEOVERLAP */
module casez_overlap_priority (
    input [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        (* priority *) casez (in_val)
            2'b00: out_res = 1'b0;
            2'b01: out_res = 1'b0;
            2'b0?: out_res = 1'b1;
            2'b1?: out_res = 1'b1;
            default: out_res = 1'b0;
        endcase
    end
endmodule
/* verilator lint_on CASEOVERLAP */
module case_unique_incomplete (
    input [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        (* unique *) case (in_val)
            2'b00: out_res = 1'b0;
            2'b01: out_res = 1'b1;
            default: out_res = 1'b0;
        endcase
    end
endmodule
/* verilator lint_off CASEX */
module casex_basic (
    input [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casex (in_val)
            3'b1xx: out_res = 1'b1;
            3'b01x: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule
/* verilator lint_on CASEX */
/* verilator lint_off CASEWITHX */
module case_with_x (
    input [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b00: out_res = 1'b0;
            2'b0x: out_res = 1'b1;
            2'b10: out_res = 1'b0;
            2'b11: out_res = 1'b1;
        endcase
    end
endmodule
/* verilator lint_on CASEWITHX */
/* verilator lint_off CASEINCOMPLETE */
module case_incomplete_with_default (
    input [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            3'b001: out_res = 1'b1;
            3'b010: out_res = 1'b0;
            3'b100: out_res = 1'b1;
            default: out_res = 1'b0;
        endcase
    end
endmodule
/* verilator lint_on CASEINCOMPLETE */
module case_many_items (
    input [3:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            4'd0: out_res = 1'b0;
            4'd1: out_res = 1'b1;
            4'd2: out_res = 1'b0;
            4'd3: out_res = 1'b1;
            4'd4: out_res = 1'b0;
            4'd5: out_res = 1'b1;
            4'd6: out_res = 1'b0;
            4'd7: out_res = 1'b1;
            4'd8: out_res = 1'b0;
            4'd9: out_res = 1'b1;
            default: out_res = 1'b0;
        endcase
    end
endmodule
/* verilator lint_off CASEWITHX */
module generate_case_if (
    input [1:0] in_val,
    output wire out_res
);
    wire [1:0] gen_in;
    reg gen_out_reg;
    assign gen_in = in_val;
    parameter CONFIG_GEN = 1;
    generate
        if (CONFIG_GEN == 1) begin : gen_case_block
            always_comb begin
                casez (gen_in)
                    2'b00: gen_out_reg = 1'b0;
                    2'b01: gen_out_reg = 1'b1;
                    2'b1?: gen_out_reg = 1'b0;
                    default: gen_out_reg = 1'b1;
                endcase
            end
            assign out_res = gen_out_reg;
        end else begin : gen_assign_block
            always_comb begin
                gen_out_reg = gen_in[0];
            end
            assign out_res = gen_out_reg;
        end
    endgenerate
endmodule
/* verilator lint_on CASEWITHX */
module case_multiple_defaults (
    input [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b00: out_res = 1'b0;
            default: out_res = 1'b1;
            2'b01: out_res = 1'b1;
        endcase
    end
endmodule
module gen_case_stmt (
    input [1:0] in_val,
    output wire out_res
);
    wire [1:0] gen_sel = in_val;
    parameter P = 1;
    generate
        case (P)
            1: begin : block_p1
                reg local_reg;
                always_comb begin
                    casez (gen_sel)
                        2'b00: local_reg = 1'b0;
                        2'b01: local_reg = 1'b1;
                        2'b1?: local_reg = 1'b0;
                        default: local_reg = 1'b1;
                    endcase
                end
                assign out_res = local_reg;
            end
            default: begin : block_p_other
                assign out_res = gen_sel[0];
            end
        endcase
    endgenerate
endmodule
module case_non_constant_cond (
    input [1:0] in_val,
    input [1:0] in_cond_val,
    output reg out_res
);
    wire [1:0] non_const_cond = in_cond_val + 1;
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            non_const_cond: out_res = 1'b1;
            2'b10: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule
module case_enum_incomplete_unique_no_default (
    input my_enum_incomplete_t in_state,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        (* unique *) case (in_state)
            STATE_A_INC: out_res = 1'b1;
            STATE_B_INC: out_res = 1'b0;
        endcase
    end
endmodule
/* verilator lint_off CASEWITHX */
module casez_item_with_x (
    input [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            3'b1xx: out_res = 1'b1;
            3'b01?: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule
/* verilator lint_on CASEWITHX */
module case_empty_statement (
    input [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b00: out_res = 1'b1;
            2'b01: ;
            2'b10: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule
