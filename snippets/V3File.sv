module basic_assign_if (
    input logic in_a,
    input logic in_b,
    output logic out_c
);
    logic intermediate_wire;
    assign intermediate_wire = in_a & in_b;
    always_comb begin
        if (intermediate_wire) begin
            out_c = 1'b1;
        end else begin
            out_c = 1'b0;
        end
    end
endmodule
module sequential_register (
    input logic clk,
    input logic reset_n,
    input logic enable_in,
    input logic data_in,
    output logic data_out
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            data_out <= 1'b0; 
        end else if (enable_in) begin
            data_out <= data_in; 
        end
    end
endmodule
module case_selector (
    input logic [1:0] sel_in,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    output logic [3:0] data_out_case
);
    always_comb begin
        case (sel_in)
            2'b00: data_out_case = data0; 
            2'b01: data_out_case = data1; 
            2'b10: data_out_case = data2; 
            default: data_out_case = data3; 
        endcase
    end
endmodule
module nested_blocks (
    input logic level1_en,
    input logic level2_en,
    input logic data_value,
    output logic result_out
);
    always_comb begin : main_block 
        result_out = 1'b0; 
        if (level1_en) begin : inner_block1 
            if (level2_en) begin : inner_block2 
                result_out = data_value;
            end 
        end 
    end 
endmodule
module function_example (
    input logic [7:0] val_in,
    input logic enable_func,
    output logic [7:0] func_out
);
    function automatic logic [7:0] double_value (input logic [7:0] input_val);
        return input_val * 2;
    endfunction 
    always_comb begin
        if (enable_func) begin
            func_out = double_value(val_in); 
        end else begin
            func_out = 8'h00;
        end
    end
endmodule
module task_example (
    input logic task_in,
    output logic task_out
);
    task automatic process_data (input logic data);
        logic temp;
        temp = data; 
    endtask 
    assign task_out = task_in;
endmodule
module keyword_import_export (
    input logic keyword_in,
    output logic keyword_out
);
    assign keyword_out = keyword_in;
endmodule
module formatting_stress (
    input logic [7:0] data_in_fmt,
    input logic sel_fmt,
    input logic enable_block_fmt,
    input logic [1:0] case_sel_fmt,
    output logic [7:0] data_out_fmt
);
    logic [7:0] temp_reg_fmt; 
    always_comb begin : stress_comb_block_label 
        data_out_fmt = 8'hXX; 
        if (enable_block_fmt) begin
            if (sel_fmt) begin
                case (case_sel_fmt) 
                    2'b00: data_out_fmt = data_in_fmt;
                    2'b01: begin 
                        data_out_fmt = ~data_in_fmt; 
                        end 
                    2'b10: begin 
                        logic [7:0] added_val; 
                        added_val = data_in_fmt + 8'h01; 
                        data_out_fmt = added_val; 
                        end 
                    default: data_out_fmt = 8'hFF; 
                endcase 
            end else begin
                data_out_fmt = data_in_fmt - 8'h01; 
            end 
        end else begin
            data_out_fmt = 8'h00; 
        end 
    end 
endmodule
module string_param_example (
    input logic dummy_in_str,
    output logic dummy_out_str
);
    parameter string MODULE_DESCRIPTION = "This is a sample module with a string parameter."; 
    assign dummy_out_str = dummy_in_str; 
endmodule
