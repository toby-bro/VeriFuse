module stmt_array_sel_postadd_task (
    input logic [7:0] data_init_in_m5,
    input logic [3:0] index_base_in_m5,
    output logic [7:0] data_out_m5,
    output logic [3:0] se_var_out_m5
);
    logic [7:0] byte_array_m5 [0:15];
    logic [3:0] index_side_effect_var_m5;
    function automatic logic [3:0] get_index_se_m5(input logic [3:0] base_idx, inout logic [3:0] se_counter);
        se_counter = se_counter + 1;
        return base_idx + se_counter[1:0];
    endfunction
    task automatic process_array_update_m5(input logic [3:0] index_base, inout logic [7:0] arr [0:15], inout logic [3:0] se_counter);
        arr [ get_index_se_m5(index_base, se_counter) ]++;
    endtask
    always_comb begin
        for (int i = 0; i < 16; i++) begin
            byte_array_m5[i] = data_init_in_m5;
        end
        index_side_effect_var_m5 = 0;
        process_array_update_m5(index_base_in_m5, byte_array_m5, index_side_effect_var_m5);
        se_var_out_m5 = index_side_effect_var_m5;
        data_out_m5 = byte_array_m5 [ index_base_in_m5 + index_side_effect_var_m5[1:0] ];
    end
endmodule

