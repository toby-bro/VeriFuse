module simple_sequential_split (
    input logic clk,
    input logic rst,
    input logic [7:0] data_in_seq,
    output logic [7:0] seq_split_out,
    output logic [7:0] seq_other_out
);
    logic [7:0] seq_split_reg (* isolate_assignments *);
    logic [7:0] seq_other_reg;
    always_ff @(posedge clk) begin
        if (rst) begin
            seq_split_reg <= 8'h00;
            seq_other_reg <= 8'hFF;
        end else begin
            seq_split_reg <= data_in_seq + 8'd1;
            seq_other_reg <= data_in_seq - 8'd1;
        end
    end
    assign seq_split_out = seq_split_reg;
    assign seq_other_out = seq_other_reg;
endmodule
module simple_combinatorial_split (
    input logic [3:0] a_comb,
    input logic [3:0] b_comb,
    output logic [3:0] comb_split_out,
    output logic [3:0] comb_other_out
);
    logic [3:0] comb_split_wire (* isolate_assignments *);
    logic [3:0] comb_other_wire;
    always_comb begin
        comb_split_wire = a_comb & b_comb;
        comb_other_wire = a_comb | b_comb;
    end
    assign comb_split_out = comb_split_wire;
    assign comb_other_out = comb_other_wire;
endmodule
module latch_split_example (
    input logic enable_latch,
    input logic [15:0] data_in_latch,
    output logic [15:0] latch_split_out,
    output logic [15:0] latch_other_out
);
    logic [15:0] latch_split_var (* isolate_assignments *);
    logic [15:0] latch_other_var;
    always @(enable_latch or data_in_latch) begin
        if (enable_latch) begin
            latch_split_var = data_in_latch + 16'd1;
            latch_other_var = data_in_latch - 16'd1;
        end else begin
            latch_split_var = 16'hAAAA;
            latch_other_var = 16'h5555;
        end
    end
    assign latch_split_out = latch_split_var;
    assign latch_other_out = latch_other_var;
endmodule
module conditional_ff_split (
    input logic clk,
    input logic rst_cond,
    input logic condition_sig,
    input logic [11:0] val_true,
    input logic [11:0] val_false,
    output logic [11:0] cond_ff_split_out,
    output logic [11:0] cond_ff_other_out
);
    logic [11:0] cond_ff_split_reg (* isolate_assignments *);
    logic [11:0] cond_ff_other_reg;
    always_ff @(posedge clk) begin
        if (rst_cond) begin
            cond_ff_split_reg <= 12'd0;
            cond_ff_other_reg <= 12'd0;
        end else begin
            if (condition_sig) begin
                cond_ff_split_reg <= val_true + 12'd5;
                cond_ff_other_reg <= val_true - 12'd5;
            end else begin
                cond_ff_split_reg <= val_false * 12'd3;
                cond_ff_other_reg <= val_false / 12'd3;
            end
        end
    end
    assign cond_ff_split_out = cond_ff_split_reg;
    assign cond_ff_other_out = cond_ff_other_reg;
endmodule
module case_comb_split (
    input logic [1:0] sel_case_comb,
    input logic [12:0] d0_case,
    input logic [12:0] d1_case,
    input logic [12:0] d2_case,
    output logic [12:0] case_comb_split_out,
    output logic [12:0] case_comb_other_out
);
    logic [12:0] case_comb_split_wire (* isolate_assignments *);
    logic [12:0] case_comb_other_wire;
    always_comb begin
        case (sel_case_comb)
            2'b00: begin
                case_comb_split_wire = d0_case + 13'd1;
                case_comb_other_wire = d0_case - 13'd1;
            end
            2'b01: begin
                case_comb_split_wire = d1_case * 13'd2;
                case_comb_other_wire = d1_case / 13'd2;
            end
            2'b10: begin
                case_comb_split_wire = d2_case & 13'hABCD;
                case_comb_other_wire = d2_case | 13'h5678;
            end
            default: begin
                case_comb_split_wire = 13'bx;
                case_comb_other_wire = 13'bx;
            end
        endcase
    end
    assign case_comb_split_out = case_comb_split_wire;
    assign case_comb_other_out = case_comb_other_wire;
endmodule
module compound_assign_ff_split (
    input logic clk,
    input logic rst_comp,
    input logic [9:0] add_val,
    input logic [9:0] sub_val,
    output logic [9:0] comp_ff_split_res,
    output logic [9:0] comp_ff_other_res
);
    logic [9:0] comp_ff_split_reg (* isolate_assignments *);
    logic [9:0] comp_ff_other_reg;
    always_ff @(posedge clk) begin
        if (rst_comp) begin
            comp_ff_split_reg <= 10'd0;
            comp_ff_other_reg <= 10'd0;
        end else begin
            comp_ff_split_reg <= comp_ff_split_reg + add_val;
            comp_ff_other_reg <= comp_ff_other_reg - sub_val;
        end
    end
    assign comp_ff_split_res = comp_ff_split_reg;
    assign comp_ff_other_res = comp_ff_other_reg;
endmodule
module multi_split_vars_comb (
    input logic [6:0] in_data_multi,
    output logic [6:0] multi_split_a_out,
    output logic [6:0] multi_split_b_out,
    output logic [6:0] multi_other_out
);
    logic [6:0] multi_split_var_a (* isolate_assignments *);
    logic [6:0] multi_split_var_b (* isolate_assignments *);
    logic [6:0] multi_other_var;
    always_comb begin
        multi_split_var_a = in_data_multi + 7'd1;
        multi_split_var_b = in_data_multi * 7'd2;
        multi_other_var = in_data_multi & 7'h3F;
    end
    assign multi_split_a_out = multi_split_var_a;
    assign multi_split_b_out = multi_split_var_b;
    assign multi_other_out = multi_other_var;
endmodule
module multi_split_vars_ff (
    input logic clk,
    input logic rst_multi,
    input logic [8:0] in_data_ff_multi,
    output logic [8:0] ff_multi_split_a_out,
    output logic [8:0] ff_multi_split_b_out,
    output logic [8:0] ff_multi_other_out
);
    logic [8:0] ff_multi_split_reg_a (* isolate_assignments *);
    logic [8:0] ff_multi_split_reg_b (* isolate_assignments *);
    logic [8:0] ff_multi_other_reg;
    always_ff @(posedge clk) begin
        if (rst_multi) begin
            ff_multi_split_reg_a <= 9'd0;
            ff_multi_split_reg_b <= 9'd0;
            ff_multi_other_reg <= 9'd0;
        end else begin
            ff_multi_split_reg_a <= in_data_ff_multi + 9'd11;
            ff_multi_split_reg_b <= in_data_ff_multi - 9'd11;
            ff_multi_other_reg <= in_data_ff_multi | 9'h1AA;
        end
    end
    assign ff_multi_split_a_out = ff_multi_split_reg_a;
    assign ff_multi_split_b_out = ff_multi_split_reg_b;
    assign ff_multi_other_out = ff_multi_other_reg;
endmodule
module func_call_comb_split (
    input logic [7:0] func_in_val,
    input logic func_select,
    output logic [7:0] func_comb_split_res,
    output logic [7:0] func_comb_other_res
);
    logic [7:0] func_comb_split_wire (* isolate_assignments *);
    logic [7:0] func_comb_other_wire;
    function automatic logic [7:0] compute_func (input logic [7:0] val_in, input logic sel);
        if (sel)
            return val_in + 8'd7;
        else
            return val_in - 8'd7;
    endfunction
    always_comb begin
        func_comb_split_wire = compute_func(func_in_val, func_select);
        func_comb_other_wire = func_in_val ^ 8'h55;
    end
    assign func_comb_split_res = func_comb_split_wire;
    assign func_comb_other_res = func_comb_other_wire;
endmodule
module struct_ff_split (
    input logic clk,
    input logic rst_struct,
    input logic [7:0] data_a_struct,
    input logic [7:0] data_b_struct,
    output logic [7:0] struct_ff_split_a_out,
    output logic [7:0] struct_ff_split_b_out,
    output logic [7:0] struct_ff_other_out
);
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } my_packed_struct_t;
    my_packed_struct_t struct_ff_split_reg (* isolate_assignments *);
    logic [7:0] struct_ff_other_reg;
    always_ff @(posedge clk) begin
        if (rst_struct) begin
            struct_ff_split_reg.field_a <= 8'd0;
            struct_ff_split_reg.field_b <= 8'd0;
            struct_ff_other_reg <= 8'd0;
        end else begin
            struct_ff_split_reg.field_a <= data_a_struct + 8'd2;
            struct_ff_split_reg.field_b <= data_b_struct * 8'd3;
            struct_ff_other_reg <= data_a_struct | data_b_struct;
        end
    end
    assign struct_ff_split_a_out = struct_ff_split_reg.field_a;
    assign struct_ff_split_b_out = struct_ff_split_reg.field_b;
    assign struct_ff_other_out = struct_ff_other_reg;
endmodule
module array_comb_split (
    input logic [3:0] data_in_arr_comb,
    input logic [1:0] index_arr_comb,
    output logic [3:0] array_comb_split_elem,
    output logic [3:0] array_comb_other_val
);
    logic [3:0] array_comb_split_wire [3:0] (* isolate_assignments *);
    logic [3:0] array_comb_other_wire;
    always_comb begin
        array_comb_split_wire[index_arr_comb] = data_in_arr_comb + 4'd1;
        array_comb_other_wire = data_in_arr_comb - 4'd1;
    end
    assign array_comb_split_elem = array_comb_split_wire[index_arr_comb];
    assign array_comb_other_val = array_comb_other_wire;
endmodule
module always_star_split (
    input logic [5:0] star_input,
    input logic star_control,
    output logic [5:0] star_split_out,
    output logic [5:0] star_other_out
);
    logic [5:0] star_split_wire (* isolate_assignments *);
    logic [5:0] star_other_wire;
    always @* begin
        if (star_control) begin
            star_split_wire = star_input + 6'd1;
            star_other_wire = star_input - 6'd1;
        end else begin
            star_split_wire = star_input * 6'd2;
            star_other_wire = star_input / 6'd2;
        end
    end
    assign star_split_out = star_split_wire;
    assign star_other_out = star_other_wire;
endmodule
module nested_if_ff_split (
    input logic clk,
    input logic rst_nest,
    input logic en_outer_nest,
    input logic en_inner_nest,
    input logic [4:0] data_nest,
    output logic [4:0] nest_ff_split_res,
    output logic [4:0] nest_ff_other_res
);
    logic [4:0] nest_ff_split_reg (* isolate_assignments *);
    logic [4:0] nest_ff_other_reg;
    always_ff @(posedge clk) begin
        if (rst_nest) begin
            nest_ff_split_reg <= 5'd0;
            nest_ff_other_reg <= 5'd0;
        end else begin
            if (en_outer_nest) begin
                nest_ff_split_reg <= data_nest + 5'd1;
                nest_ff_other_reg <= data_nest - 5'd1;
                if (en_inner_nest) begin
                    nest_ff_split_reg <= nest_ff_split_reg * 5'd2;
                    nest_ff_other_reg <= nest_ff_other_reg / 5'd2;
                end else begin
                    nest_ff_split_reg <= nest_ff_split_reg + 5'd10;
                    nest_ff_other_reg <= nest_ff_other_reg - 5'd10;
                end
            end else begin
                nest_ff_split_reg <= data_nest | 5'h1F;
                nest_ff_other_reg <= data_nest & 5'h0A;
            end
        end
    end
    assign nest_ff_split_res = nest_ff_split_reg;
    assign nest_ff_other_res = nest_ff_other_reg;
endmodule
module signed_ff_split (
    input logic clk,
    input logic rst_signed,
    input signed logic [7:0] data_in_signed,
    output signed logic [7:0] signed_ff_split_out,
    output signed logic [7:0] signed_ff_other_out
);
    signed logic [7:0] signed_ff_split_reg (* isolate_assignments *);
    signed logic [7:0] signed_ff_other_reg;
    always_ff @(posedge clk) begin
        if (rst_signed) begin
            signed_ff_split_reg <= 8'd0;
            signed_ff_other_reg <= 8'd0;
        end else begin
            signed_ff_split_reg <= data_in_signed + 8'd5;
            signed_ff_other_reg <= data_in_signed - 8'd5;
        end
    end
    assign signed_ff_split_out = signed_ff_split_reg;
    assign signed_ff_other_out = signed_ff_other_reg;
endmodule
module part_select_comb_split (
    input logic [15:0] data_in_part,
    input logic [2:0] sel_part,
    output logic [7:0] part_split_out,
    output logic [7:0] part_other_out
);
    logic [15:0] part_split_var (* isolate_assignments *);
    logic [7:0] part_other_var;
    always_comb begin
        part_split_var[7:0] = data_in_part[7:0] + 8'd1;
        part_split_var[15:8] = data_in_part[15:8] - 8'd1;
        part_other_var = data_in_part[7:0] ^ data_in_part[15:8];
    end
    assign part_split_out = part_split_var[7:0];
    assign part_other_out = part_other_var;
endmodule
module bit_select_ff_split (
    input logic clk,
    input logic rst_bit,
    input logic [7:0] data_in_bit,
    input logic [2:0] sel_bit,
    output logic [7:0] bit_split_out,
    output logic [7:0] bit_other_out
);
    logic [7:0] bit_split_reg (* isolate_assignments *);
    logic [7:0] bit_other_reg;
    always_ff @(posedge clk) begin
        if (rst_bit) begin
            bit_split_reg <= 8'h00;
            bit_other_reg <= 8'hFF;
        end else begin
            bit_split_reg[sel_bit] <= data_in_bit[sel_bit] + 1'b1;
            bit_split_reg[7-sel_bit] <= data_in_bit[7-sel_bit] - 1'b1;
            bit_other_reg <= data_in_bit;
        end
    end
    assign bit_split_out = bit_split_reg;
    assign bit_other_out = bit_other_reg;
endmodule
module nested_if_case_comb_split (
    input logic control_if,
    input logic [1:0] control_case,
    input logic [9:0] data_a,
    input logic [9:0] data_b,
    input logic [9:0] data_c,
    output logic [9:0] nested_split_out,
    output logic [9:0] nested_other_out
);
    logic [9:0] nested_split_var (* isolate_assignments *);
    logic [9:0] nested_other_var;
    always_comb begin
        if (control_if) begin
            case (control_case)
                2'b00: begin
                    nested_split_var = data_a + 10'd1;
                    nested_other_var = data_a - 10'd1;
                end
                2'b01: begin
                    nested_split_var = data_b * 10'd2;
                    nested_other_var = data_b / 10'd2;
                end
                default: begin
                    nested_split_var = data_c & 10'h3FF;
                    nested_other_var = data_c | 10'h200;
                end
            endcase
        end else begin
            nested_split_var = data_a ^ data_b;
            nested_other_var = data_b | data_c;
        end
    end
    assign nested_split_out = nested_split_var;
    assign nested_other_out = nested_other_var;
endmodule
