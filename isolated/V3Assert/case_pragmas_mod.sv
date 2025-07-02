module case_full_parallel_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        (* full, parallel *)
        case (case_expr)
            2'b00: internal_out = 1;
            2'b01: internal_out = 2;
            2'b10: internal_out = 3;
            default: internal_out = 4;
        endcase
    end
endmodule

module case_full_simple_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        (* full *)
        case (case_expr)
            2'b00: internal_out = 10;
            2'b01: internal_out = 11;
            2'b10: internal_out = 12;
            default: internal_out = 13;
        endcase
    end
endmodule

module case_parallel_simple_mod (
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        (* parallel *)
        case (case_inside_val)
            4'd0, 4'd1: internal_out = 14;
            4'd2, 4'd3: internal_out = 15;
            default: internal_out = 18;
        endcase
    end
endmodule

module case_priority_casex_complex_mod (
    input logic [1:0] case_expr,
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        priority casex ({case_expr, case_inside_val[1:0]})
            4'b1???: internal_out = 24;
            4'b?1??: internal_out = 25;  
            4'b??1?: internal_out = 26;  
            4'b???1: internal_out = 27;  
            4'b0000: internal_out = 28;  
            default: internal_out = 29;
        endcase
    end
endmodule

module case_priority_overlapping_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        priority casez (case_expr)
            2'b1?: internal_out = 5;
            2'b?1: internal_out = 6;  
            2'b0?: internal_out = 7;
            2'b?0: internal_out = 8;  
            default: internal_out = 9;
        endcase
    end
endmodule

module case_unique0_inside_no_default_mod (
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        unique0 case (case_inside_val)
            case_inside_val inside {4'd10, 4'd11}: internal_out = 19;
            case_inside_val inside {4'd11, 4'd12}: internal_out = 20;  
            case_inside_val inside {[4'd10:4'd13]}: internal_out = 21;  
            case_inside_val inside {4'd14, 4'd15}: internal_out = 22;
            case_inside_val inside {4'd15}: internal_out = 23;  
        endcase
    end
endmodule

module case_unique0_violating_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        unique0 casez (case_expr)
            2'b1?: internal_out = 8;
            2'b11: internal_out = 9;  
            2'b?1: internal_out = 10; 
            2'b00: internal_out = 11; 
        endcase
    end
endmodule

module case_unique_casez_reordered_mod (
    input logic [1:0] case_expr,
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        unique casez ({case_expr[0], case_inside_val[3:2], case_expr[1]})
            4'b1?0?: internal_out = 30;
            4'b?101: internal_out = 31;  
            4'b0?1?: internal_out = 32;
            4'b1?1?: internal_out = 33;  
            4'b?111: internal_out = 34;  
        endcase
    end
endmodule

module case_unique_inside_overlapping_mod (
    input logic [3:0] case_inside_val,
    input logic [3:0] range_end,
    input logic [3:0] range_start,
    output logic [4:0] internal_out
);
    always @* begin
        unique case (case_inside_val)
            case_inside_val inside {[range_start:range_end]}: internal_out = 16;
            case_inside_val inside {4'd0, 4'd1, 4'd2}: internal_out = 17;  
            case_inside_val inside {4'd8, 4'd9}: internal_out = 18;
            case_inside_val inside {[4'd7:4'd10]}: internal_out = 19;  
            case_inside_val inside {4'd15}: internal_out = 20;  
            default: internal_out = 21;  
        endcase
    end
endmodule

module case_pragmas_mod (
    input logic [1:0] case_expr,
    input logic [3:0] case_inside_val,
    input logic [3:0] range_end,
    input logic [3:0] range_start,
    output logic case_pragma_out
);
    logic [4:0] out1, out2, out3, out4, out5, out6, out7, out8, out9;
    logic [4:0] combined_out;
    case_full_parallel_mod u1 (
        .internal_out(out1),
        .case_expr(case_expr)
    );
    case_priority_overlapping_mod u2 (
        .internal_out(out2),
        .case_expr(case_expr)
    );
    case_unique0_violating_mod u3 (
        .internal_out(out3),
        .case_expr(case_expr)
    );
    case_full_simple_mod u4 (
        .internal_out(out4),
        .case_expr(case_expr)
    );
    case_parallel_simple_mod u5 (
        .internal_out(out5),
        .case_inside_val(case_inside_val)
    );
    case_unique_inside_overlapping_mod u6 (
        .internal_out(out6),
        .case_inside_val(case_inside_val),
        .range_start(range_start),
        .range_end(range_end)
    );
    case_unique0_inside_no_default_mod u7 (
        .internal_out(out7),
        .case_inside_val(case_inside_val)
    );
    case_priority_casex_complex_mod u8 (
        .internal_out(out8),
        .case_expr(case_expr),
        .case_inside_val(case_inside_val)
    );
    case_unique_casez_reordered_mod u9 (
        .internal_out(out9),
        .case_expr(case_expr),
        .case_inside_val(case_inside_val)
    );
    always @* begin
        combined_out = out1 ^ out2 ^ out3 ^ out4 ^ out5 ^ out6 ^ out7 ^ out8 ^ out9;
    end
    assign case_pragma_out = combined_out[0] ^ combined_out[4] ^ (|combined_out[3:1]);
endmodule

