module tristate_bufif1(
    input logic data_in,
    input logic enable_in,
    inout tri tristate_port_io,
    output logic read_data_out
);
    bufif1 instance_bufif1 (tristate_port_io, data_in, enable_in);
    assign read_data_out = tristate_port_io;
endmodule
module tristate_bufif0(
    input logic data_in,
    input logic enable_in,
    inout tri tristate_port_io,
    output logic read_data_out
);
    bufif0 instance_bufif0 (tristate_port_io, data_in, enable_in);
    assign read_data_out = tristate_port_io;
endmodule
module tristate_notif1(
    input logic data_in,
    input logic enable_n_in,
    inout tri out_port_io,
    output logic read_port_out
);
    notif1 instance_notif1 (out_port_io, data_in, enable_n_in);
    assign read_port_out = out_port_io;
endmodule
module tristate_notif0(
    input logic data_in,
    input logic enable_p_in,
    inout tri out_port_io,
    output logic read_port_out
);
    notif0 instance_notif0 (out_port_io, data_in, enable_p_in);
    assign read_port_out = out_port_io;
endmodule
module tristate_pullup_primitive(
    input logic dummy_in,
    inout tri pulled_wire_prim_io,
    output logic read_pulled_wire_out
);
    pullup(pulled_wire_prim_io);
    assign read_pulled_wire_out = pulled_wire_prim_io;
endmodule
module tristate_pulldown_primitive(
    input logic dummy_in,
    inout tri pulled_wire_prim_pd_io,
    output logic read_pulled_wire_pd_out
);
    pulldown(pulled_wire_prim_pd_io);
    assign read_pulled_wire_pd_out = pulled_wire_prim_pd_io;
endmodule
module tristate_inout_pullup_decl(
    input logic enable_in,
    inout (pullup, pullup) tri pulled_port,
    output logic read_port
);
    assign pulled_port = enable_in ? 1'b0 : 1'bz;
    assign read_port = pulled_port;
endmodule
module tristate_inout_pulldown_decl(
    input logic enable_in,
    inout (pulldown, pulldown) tri pulled_port_pd,
    output logic read_port_pd
);
    assign pulled_port_pd = enable_in ? 1'b1 : 1'bz;
    assign read_port_pd = pulled_port_pd;
endmodule
module tristate_wor_multidrive(
    input logic [3:0] data_a,
    input logic en_a,
    input logic [3:0] data_b,
    input logic en_b,
    output wor [3:0] output_wire,
    output logic [3:0] read_output
);
    assign output_wire = en_a ? data_a : 4'bz;
    assign output_wire = en_b ? data_b : 4'bz;
    assign read_output = output_wire;
endmodule
module tristate_wand_multidrive(
    input logic [3:0] data_c,
    input logic en_c,
    input logic [3:0] data_d,
    input logic en_d,
    output wand [3:0] output_wire_and,
    output logic [3:0] read_output_and
);
    assign output_wire_and = en_c ? data_c : 4'bz;
    assign output_wire_and = en_d ? data_d : 4'bz;
    assign read_output_and = output_wire_and;
endmodule
module tristate_trior_multidrive(
    input logic [2:0] data_e,
    input logic en_e,
    input logic [2:0] data_f,
    input logic en_f,
    output trior [2:0] output_wire_trior,
    output logic [2:0] read_output_trior
);
    assign output_wire_trior = en_e ? data_e : 3'bz;
    assign output_wire_trior = en_f ? data_f : 3'bz;
    assign read_output_trior = output_wire_trior;
endmodule
module tristate_triand_multidrive(
    input logic [2:0] data_g,
    input logic en_g,
    input logic [2:0] data_h,
    input logic en_h,
    output triand [2:0] output_wire_triand,
    output logic [2:0] read_output_triand
);
    assign output_wire_triand = en_g ? data_g : 3'bz;
    assign output_wire_triand = en_h ? data_h : 3'bz;
    assign read_output_triand = output_wire_triand;
endmodule
module tristate_strength_wor(
    input logic [2:0] data_low,
    input logic en_low,
    input logic [2:0] data_high,
    input logic en_high,
    output wor [2:0] output_wor_str,
    output logic [2:0] read_output_str
);
    tri [2:0] tri_low = en_low ? data_low : 3'bz;
    tri [2:0] tri_high = en_high ? data_high : 3'bz;
    assign (weak1, weak0) output_wor_str = tri_low;
    assign (strong1, strong0) output_wor_str = tri_high;
    assign read_output_str = output_wor_str;
endmodule
module tristate_strength_wand(
    input logic [2:0] data_low,
    input logic en_low,
    input logic [2:0] data_high,
    input logic en_high,
    output wand [2:0] output_wand_str,
    output logic [2:0] read_output_str_and
);
    tri [2:0] tri_low = en_low ? data_low : 3'bz;
    tri [2:0] tri_high = en_high ? data_high : 3'bz;
    assign (weak1, weak0) output_wand_str = tri_low;
    assign (strong1, strong0) output_wand_str = tri_high;
    assign read_output_str_and = output_wand_str;
endmodule
module tristate_logic_ops(
    input logic [3:0] data1,
    input logic en1,
    input logic [3:0] data2,
    input logic en2,
    output logic [3:0] out_and,
    output logic [3:0] out_or,
    output logic [3:0] out_not
);
    tri [3:0] tri1;
    tri [3:0] tri2;
    assign tri1 = en1 ? data1 : 4'bz;
    assign tri2 = en2 ? data2 : 4'bz;
    assign out_and = tri1 & tri2;
    assign out_or = tri1 | tri2;
    assign out_not = ~tri1;
endmodule
module tristate_concat_rhs(
    input logic [3:0] data_hi,
    input logic en_hi,
    input logic [3:0] data_lo,
    input logic en_lo,
    output logic [7:0] output_concat
);
    tri [3:0] tri_hi;
    tri [3:0] tri_lo;
    assign tri_hi = en_hi ? data_hi : 4'bz;
    assign tri_lo = en_lo ? data_lo : 4'bz;
    assign output_concat = {tri_hi, tri_lo};
endmodule
module tristate_slice_rhs(
    input logic [7:0] data_in,
    input logic en_in,
    input logic [2:0] select_idx,
    output logic output_select
);
    tri [7:0] tri_wire;
    assign tri_wire = en_in ? data_in : 8'bz;
    assign output_select = tri_wire[select_idx];
endmodule
module tristate_indexed_rhs(
    input logic [7:0] data_in,
    input logic en_in,
    input logic [2:0] index,
    output logic output_indexed
);
    tri [7:0] tri_wire;
    assign tri_wire = en_in ? data_in : 8'bz;
    assign output_indexed = tri_wire[index];
endmodule
module tristate_slice_lhs(
    input logic [7:0] in_data,
    input logic in_en,
    output tri [7:0] sliced_output
);
    tri [7:0] internal_tri;
    assign internal_tri = in_en ? in_data : 8'bz;
    assign sliced_output = 8'b0;
    assign sliced_output[3:0] = internal_tri[3:0];
endmodule
module tristate_indexed_lhs(
    input logic [7:0] in_data,
    input logic in_en,
    input logic [2:0] index,
    output tri [7:0] indexed_output
);
    tri [7:0] internal_tri;
    assign internal_tri = in_en ? in_data : 8'bz;
    assign indexed_output = 8'b0;
    assign indexed_output[index] = internal_tri[index];
endmodule
module tristate_signed_extend(
    input logic [2:0] data_in,
    input logic en_in,
    output logic [4:0] extended_signed_out
);
    tri [2:0] tri_wire = en_in ? data_in : 3'bz;
    assign extended_signed_out = $signed(tri_wire);
endmodule
module tristate_unsigned_extend(
    input logic [2:0] data_in,
    input logic en_in,
    output logic [4:0] extended_unsigned_out
);
    tri [2:0] tri_wire = en_in ? data_in : 3'bz;
    assign extended_unsigned_out = $unsigned(tri_wire);
endmodule
module tristate_compare_case_eq(
    input tri [2:0] tri_in,
    input logic [2:0] compare_val,
    output logic match_eq
);
    assign match_eq = (tri_in === compare_val);
endmodule
module tristate_compare_case_neq(
    input tri [2:0] tri_in,
    input logic [2:0] compare_val,
    output logic match_neq
);
    assign match_neq = (tri_in !== compare_val);
endmodule
module tristate_compare_wildcard_eq(
    input tri [3:0] tri_in_wild,
    input logic [3:0] compare_val_wild,
    output logic match_eq_wild
);
    assign match_eq_wild = (tri_in_wild ==? compare_val_wild);
endmodule
module tristate_compare_wildcard_neq(
    input tri [3:0] tri_in_wild,
    input logic [3:0] compare_val_wild,
    output logic match_neq_wild
);
    assign match_neq_wild = (tri_in_wild !=? compare_val_wild);
endmodule
module tristate_countbits_all(
    input tri [7:0] tri_vector,
    input logic dummy_in,
    output logic [3:0] count_ones,
    output logic [3:0] count_zeros,
    output logic [3:0] count_x,
    output logic [3:0] count_z
);
    assign count_ones = $countbits('1, tri_vector);
    assign count_zeros = $countbits('0, tri_vector);
    assign count_x = $countbits('x, tri_vector);
    assign count_z = $countbits('z, tri_vector);
endmodule
module tristate_conditional(
    input logic condition,
    input logic [2:0] data_then,
    input logic en_then,
    input logic [2:0] data_else,
    input logic en_else,
    output logic [2:0] result_out
);
    tri [2:0] tri_then = en_then ? data_then : 3'bz;
    tri [2:0] tri_else = en_else ? data_else : 3'bz;
    assign result_out = condition ? tri_then : tri_else;
endmodule
module tristate_assign_const_z(
    input logic dummy_in,
    output tri [1:0] out_assign_z
);
    assign out_assign_z = 2'bz;
endmodule
module tristate_assign_cond_z(
    input logic condition,
    input logic [1:0] data_in,
    output tri [1:0] out_cond_z
);
    assign out_cond_z = condition ? data_in : 2'bz;
endmodule
module tristate_undriven_inout(
    input logic dummy_in,
    inout tri undriven_port,
    output logic read_undriven_port
);
    assign read_undriven_port = undriven_port;
endmodule
module tristate_multidrive_mixed_strength(
    input logic [1:0] data_s,
    input logic en_s,
    input logic [1:0] data_w,
    input logic en_w,
    output wor [1:0] resolved_output,
    output logic [1:0] read_resolved
);
    tri [1:0] tri_s = en_s ? data_s : 2'bz;
    tri [1:0] tri_w = en_w ? data_w : 2'bz;
    assign (strong1, strong0) resolved_output = tri_s;
    assign (weak1, weak0) resolved_output = tri_w;
    assign read_resolved = resolved_output;
endmodule
module tristate_multidrive_const_override(
    input logic [3:0] data_in,
    input logic en_in,
    output wor [3:0] resolved_out,
    output logic [3:0] read_resolved
);
    tri [3:0] tri_out = en_in ? data_in : 4'bz;
    assign resolved_out = tri_out;
    assign resolved_out = 4'b1010;
    assign read_resolved = resolved_out;
endmodule
module tristate_casez(
    input tri [3:0] tri_input,
    input logic dummy_in,
    output logic [1:0] case_output
);
    tri [3:0] internal_tri = tri_input;
    always_comb begin
        casez (internal_tri)
            4'b10?z: case_output = 2'b01;
            4'b?101: case_output = 2'b10;
            default: case_output = 2'b00;
        endcase
    end
endmodule
module tristate_casez_xz_pattern(
    input tri [3:0] tri_input_xz,
    input logic dummy_in,
    output logic [1:0] case_output_xz
);
    tri [3:0] internal_tri_xz = tri_input_xz;
    always_comb begin
        casez (internal_tri_xz)
            4'b1X0Z: case_output_xz = 2'b01;
            4'b?10X: case_output_xz = 2'b10;
            default: case_output_xz = 2'b00;
        endcase
    end
endmodule
module tristate_assign_strength(
    input logic [1:0] data_s,
    input logic en_s,
    output tri [1:0] wired_out,
    output logic [1:0] read_wired
);
    tri [1:0] tri_s = en_s ? data_s : 2'bz;
    assign (strong1, strong0) wired_out = tri_s;
    assign read_wired = wired_out;
endmodule
module child_tristate_hier_basic(
    input logic child_enable,
    input logic child_data,
    inout tri child_port,
    output logic child_read_port
);
    bufif1 instance_child_bufif1 (child_port, child_data, child_enable);
    assign child_read_port = child_port;
endmodule
module parent_tristate_hier_basic(
    input logic parent_enable,
    input logic parent_data,
    output logic parent_out
);
    tri intermediate_tri_wire;
    logic dummy_child_read;
    child_tristate_hier_basic child_inst (
        .child_enable(parent_enable),
        .child_data(parent_data),
        .child_port(intermediate_tri_wire),
        .child_read_port(dummy_child_read)
    );
    assign parent_out = intermediate_tri_wire;
endmodule
module child_tristate_inout_slice(
    input logic child_enable,
    input logic [3:0] child_data,
    inout tri logic [3:0] child_port,
    output logic dummy_out
);
    assign child_port = child_enable ? child_data : 4'bz;
    assign dummy_out = child_port[0];
endmodule
module parent_tristate_inout_slice(
    input logic parent_enable,
    input logic [3:0] parent_data,
    output logic [3:0] sliced_output
);
    tri [7:0] intermediate_wire;
    logic dummy_child_out;
    child_tristate_inout_slice child_inst (
        .child_enable(parent_enable),
        .child_data(parent_data),
        .child_port(intermediate_wire[3:0]),
        .dummy_out(dummy_child_out)
    );
    assign sliced_output = intermediate_wire[3:0];
endmodule
module child_tristate_inout_index(
    input logic child_enable,
    input logic child_data,
    inout tri child_port,
    output logic dummy_out
);
    assign child_port = child_enable ? child_data : 1'bz;
    assign dummy_out = child_port;
endmodule
module parent_tristate_inout_index(
    input logic parent_enable,
    input logic parent_data,
    output logic indexed_output
);
    tri [7:0] intermediate_wire;
    logic dummy_child_out;
    child_tristate_inout_index child_inst (
        .child_enable(parent_enable),
        .child_data(parent_data),
        .child_port(intermediate_wire[5]),
        .dummy_out(dummy_child_out)
    );
    assign indexed_output = intermediate_wire[5];
endmodule
module module_with_input_port(
    input logic [3:0] in_port,
    output logic [3:0] out_port
);
    assign out_port = in_port;
endmodule
module tristate_hier_pin_concat(
    input logic [3:0] tri_data,
    input logic tri_en,
    input logic dummy_bit,
    output logic [3:0] output_from_instance
);
    tri [3:0] tri_wire = tri_en ? tri_data : 4'bz;
    module_with_input_port instance_concat (
        .in_port({dummy_bit, tri_wire[2:0]}),
        .out_port(output_from_instance)
    );
endmodule
module tristate_hier_pin_select(
    input logic [7:0] tri_data,
    input logic tri_en,
    input logic [7:0] dummy_in,
    output logic [3:0] output_from_instance
);
    tri [7:0] tri_wire = tri_en ? tri_data : 8'bz;
    tri [7:0] combined_wire = tri_wire | dummy_in;
    module_with_input_port instance_select (
        .in_port(combined_wire[6:3]),
        .out_port(output_from_instance)
    );
endmodule
module tristate_shift_right(
    input tri [7:0] data_in,
    input logic en_in,
    input logic [2:0] shift_by,
    output logic [7:0] shifted_out
);
    tri [7:0] tri_wire = en_in ? data_in : 8'bz;
    assign shifted_out = tri_wire >> shift_by;
endmodule
module tristate_shift_left(
    input tri [7:0] data_in,
    input logic en_in,
    input logic [2:0] shift_by,
    output logic [7:0] shifted_out
);
    tri [7:0] tri_wire = en_in ? data_in : 8'bz;
    assign shifted_out = tri_wire << shift_by;
endmodule
module tristate_multiple_assign_tri_wire(
    input logic [3:0] data_a,
    input logic en_a,
    input logic [3:0] data_b,
    input logic en_b,
    output tri [3:0] output_wire,
    output logic [3:0] read_output
);
    assign output_wire = en_a ? data_a : 4'bz;
    assign output_wire = en_b ? data_b : 4'bz;
    assign read_output = output_wire;
endmodule
module tristate_always_comb_assign(
    input logic [3:0] data_in,
    input logic en_in,
    output tri [3:0] comb_output,
    output logic [3:0] read_output
);
    always_comb begin
        if (en_in)
            comb_output = data_in;
        else
            comb_output = 4'bz;
    end
    assign read_output = comb_output;
endmodule
module child_tristate_array_port(
    input logic enable_arr,
    input logic [3:0] data_arr_0,
    input logic [3:0] data_arr_1,
    inout tri logic [3:0] port_arr [0:1],
    output logic read_arr_0,
    output logic read_arr_1
);
    assign port_arr[0] = enable_arr ? data_arr_0 : 4'bz;
    assign port_arr[1] = enable_arr ? data_arr_1 : 4'bz;
    assign read_arr_0 = port_arr[0][0];
    assign read_arr_1 = port_arr[1][0];
endmodule
module parent_tristate_hier_pin_array(
    input logic parent_enable,
    input logic [3:0] parent_data_0,
    input logic [3:0] parent_data_1,
    output logic [3:0] read_parent_arr_0,
    output logic [3:0] read_parent_arr_1
);
    tri logic [3:0] intermediate_tri_arr [0:1];
    logic dummy_read_0, dummy_read_1;
    child_tristate_array_port child_inst (
        .enable_arr(parent_enable),
        .data_arr_0(parent_data_0),
        .data_arr_1(parent_data_1),
        .port_arr(intermediate_tri_arr),
        .read_arr_0(dummy_read_0),
        .read_arr_1(dummy_read_1)
    );
    assign read_parent_arr_0 = intermediate_tri_arr[0];
    assign read_parent_arr_1 = intermediate_tri_arr[1];
endmodule
