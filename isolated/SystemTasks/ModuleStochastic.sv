module ModuleStochastic (
    input wire [31:0] add_item_in,
    input wire [31:0] add_weight_in,
    input wire enable_stochastic,
    input wire [31:0] exam_index_in,
    input wire [31:0] seed1,
    input wire [31:0] seed2,
    input wire [31:0] seed3,
    output reg [31:0] q_handle_out,
    output reg [31:0] q_item_out,
    output reg [31:0] q_status_out,
    output reg [31:0] q_weight_out
);
integer q_handle;
integer add_success;
integer removed_item, removed_weight, removed_status;
integer exam_item, exam_weight;
integer is_full_var;
integer dummy_output_qfull; 
always @* begin
    q_handle_out = 0;
    q_item_out = 0;
    q_weight_out = 0;
    q_status_out = 0;
    if (enable_stochastic) begin
        $q_initialize(seed1, seed2, seed3, q_handle);
        q_handle_out = q_handle;
        $q_add(q_handle, add_item_in, add_weight_in, add_success);
        q_status_out = add_success; 
        $q_remove(q_handle, removed_item, removed_weight, removed_status);
        q_item_out = removed_item; 
        q_weight_out = removed_weight;
        $q_exam(q_handle, exam_index_in, exam_item, exam_weight);
        q_item_out = exam_item;
        q_weight_out = exam_weight;
        is_full_var = $q_full(q_handle, dummy_output_qfull);
        q_status_out = is_full_var; 
    end
end
endmodule

