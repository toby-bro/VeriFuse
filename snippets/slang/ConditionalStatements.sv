module mod_if_else_simple(
    input bit [3:0] in_data,
    output bit [3:0] out_result
);
always_comb begin
    if (in_data > 8) begin
        out_result = in_data + 1;
    end else begin
        out_result = in_data - 1;
    end
end
endmodule
module mod_if_elseif_chained(
    input bit [7:0] in_value,
    output bit [2:0] out_category
);
always_comb begin
    if (in_value < 10) begin
        out_category = 3'd0;
    end else if (in_value < 50) begin
        out_category = 3'd1;
    end else if (in_value < 100) begin
        out_category = 3'd2;
    end else begin
        out_category = 3'd3;
    end
end
endmodule
module mod_if_unique(
    input bit [1:0] in_sel,
    output bit out_unique
);
always_comb begin
    unique if (in_sel == 2'b00) begin
        out_unique = 1'b1;
    end else if (in_sel == 2'b01) begin
        out_unique = 1'b0;
    end else begin
        out_unique = 1'b1;
    end
end
endmodule
module mod_if_priority_no_else(
    input bit [1:0] in_sel,
    output bit out_priority
);
always_comb begin
    out_priority = 1'b0;
    priority if (in_sel == 2'b00) begin
        out_priority = 1'b1;
    end else if (in_sel == 2'b01) begin
        out_priority = 1'b0;
    end
end
endmodule
module mod_case_standard(
    input bit [7:0] in_cmd,
    output bit [3:0] out_status
);
always_comb begin
    case (in_cmd)
        8'd0, 8'd1, 8'd2: begin
            out_status = 4'hA;
        end
        8'd3, 8'd4: begin
            out_status = 4'hB;
        end
        default: begin
            out_status = 4'hF;
        end
    endcase
end
endmodule
module mod_casez_wildcard(
    input bit [3:0] in_mask_z,
    output bit [1:0] out_match_type_z
);
always_comb begin
    casez (in_mask_z)
        4'b10?0: begin
            out_match_type_z = 2'b00;
        end
        4'b011?: begin
            out_match_type_z = 2'b01;
        end
        default: begin
            out_match_type_z = 2'b11;
        end
    endcase
end
endmodule
module mod_casex_wildcard_overlap_priority(
    input bit [3:0] in_mask_x,
    output bit [1:0] out_match_type_x
);
always_comb begin
    out_match_type_x = 2'b01;
    priority casex (in_mask_x)
        4'b1X0Z: begin
             out_match_type_x = 2'b10;
        end
        4'b10?Z: begin
             out_match_type_x = 2'b11;
        end
        4'bZ1?X: begin
             out_match_type_x = 2'b00;
        end
        default: begin
             out_match_type_x = 2'b01;
        end
    endcase
end
endmodule
module mod_case_inside_range(
    input int in_level,
    output bit [1:0] out_level_cat
);
always_comb begin
    case (in_level) inside
        [1:10]: begin
            out_level_cat = 2'b00;
        end
        [11:50], [100:200]: begin
            out_level_cat = 2'b01;
        end
        default: begin
            out_level_cat = 2'b11;
        end
    endcase
end
endmodule
module mod_case_unique_priority(
    input bit [2:0] in_state_case,
    output bit out_unique_case,
    output bit out_priority_case
);
always_comb begin
    out_unique_case = 1'b0;
    unique case (in_state_case)
        3'd0: out_unique_case = 1'b0;
        3'd1: out_unique_case = 1'b1;
        3'd2: out_unique_case = 1'b0;
        3'd1: out_unique_case = 1'b1;
        default: out_unique_case = 1'b1;
    endcase
end
always_comb begin
    out_priority_case = 1'b0;
    priority case (in_state_case)
        3'd0: out_priority_case = 1'b0;
        3'd1: out_priority_case = 1'b1;
        3'd2: out_priority_case = 1'b0;
        3'd1: out_priority_case = 1'b1;
        default: out_priority_case = 1'b1;
    endcase
end
endmodule
typedef struct packed {
    logic [3:0] id;
    logic [7:0] data;
} my_packet_t;
module mod_case_matches_pattern(
    input my_packet_t in_packet,
    input bit [7:0] in_threshold,
    output bit [1:0] out_pattern_match_type
);
always_comb begin
    out_pattern_match_type = 2'b11;
    // Rewritten from illegal 'case ... matches' with assignment patterns
    if (in_packet.id == 4'hA) begin
        out_pattern_match_type = 2'b00;
    end else if (in_packet.id == 4'hB && in_packet.data > in_threshold) begin
        out_pattern_match_type = 2'b01;
    end else if (in_packet.id == 4'hC && in_packet.data == 8'd5) begin // Use a legal id for var_id
        out_pattern_match_type = 2'b10;
    end else begin
        out_pattern_match_type = 2'b11;
    end
end
endmodule
typedef enum { STATE_IDLE, STATE_READ, STATE_WRITE, STATE_ERROR } fsm_state_e;
module mod_case_enum_no_default(
    input fsm_state_e in_state_enum,
    output bit [1:0] out_action_code
);
always_comb begin
    out_action_code = 2'b11;
    case (in_state_enum)
        STATE_IDLE: begin
            out_action_code = 2'b00;
        end
        STATE_READ, STATE_WRITE: begin
            out_action_code = 2'b01;
        end
    endcase
end
endmodule
