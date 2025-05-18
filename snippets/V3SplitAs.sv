module mod_split_comb (
    input logic [7:0] data_in,
    input logic enable,
    output logic [7:0] out_a,
    output logic [7:0] out_b
);
    logic [7:0] /* isolate_assignments */ split_comb_var;
    logic [7:0] other_comb_var;
    always_comb begin
        split_comb_var = 8'b0; 
        other_comb_var = 8'b0;
        if (enable) begin
            split_comb_var = data_in;
            other_comb_var = data_in + 1;
        end
        out_a = split_comb_var;
        out_b = other_comb_var;
    end
endmodule
module mod_split_ff (
    input logic clk,
    input logic reset,
    input logic [7:0] data_in,
    output logic [7:0] out_reg_a,
    output logic [7:0] out_reg_b
);
    logic [7:0] /* isolate_assignments */ split_reg_var;
    logic [7:0] other_reg_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_reg_var <= 8'b0;
            other_reg_var <= 8'b0;
            out_reg_a <= 8'b0;
            out_reg_b <= 8'b0;
        end else begin
            split_reg_var <= data_in;
            other_reg_var <= data_in + 2;
            out_reg_a <= split_reg_var;
            out_reg_b <= other_reg_var;
        end
    end
endmodule
module mod_split_if (
    input logic clk,
    input logic reset,
    input logic cond,
    input logic [7:0] data_in,
    output logic [7:0] out_if_a,
    output logic [7:0] out_if_b
);
    logic [7:0] /* isolate_assignments */ split_if_var;
    logic [7:0] other_if_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_if_var <= 8'b0;
            other_if_var <= 8'b0;
        end else begin
            if (cond) begin
                split_if_var <= data_in;
                other_if_var <= data_in + 3;
            end else begin
                split_if_var <= data_in - 1;
                other_if_var <= data_in - 2;
            end
        end
    end
    always_comb begin
        out_if_a = split_if_var;
        out_if_b = other_if_var;
    end
endmodule
module mod_split_case (
    input logic [1:0] sel,
    input logic [7:0] data_in,
    output logic [7:0] out_case_a,
    output logic [7:0] out_case_b
);
    logic [7:0] /* isolate_assignments */ split_case_var;
    logic [7:0] other_case_var;
    always_comb begin
        split_case_var = 8'hFF;
        other_case_var = 8'hAA;
        case (sel)
            2'b00: begin
                split_case_var = data_in + 5;
                other_case_var = data_in + 6;
            end
            2'b01: begin
                split_case_var = data_in - 5;
                other_case_var = data_in - 6;
            end
            default: begin
                split_case_var = data_in;
                other_case_var = data_in;
            end
        endcase
        out_case_a = split_case_var;
        out_case_b = other_case_var;
    end
endmodule
module mod_split_multiple_vars (
    input logic clk,
    input logic reset,
    input logic [7:0] data_in,
    output logic [7:0] out_mv_a,
    output logic [7:0] out_mv_b,
    output logic [7:0] out_mv_c
);
    logic [7:0] /* isolate_assignments */ split_mv_var;
    logic [7:0] other_mv_var1;
    logic [7:0] other_mv_var2;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_mv_var <= 8'b0;
            other_mv_var1 <= 8'b0;
            other_mv_var2 <= 8'b0;
        end else begin
            split_mv_var <= data_in;
            other_mv_var1 <= data_in + 1;
            other_mv_var2 <= data_in + 2;
            if (data_in > 100) begin
                split_mv_var <= 8'hFF;
            end
            out_mv_a <= split_mv_var;
            out_mv_b <= other_mv_var1;
            out_mv_c <= other_mv_var2;
        end
    end
endmodule
module mod_split_nested (
    input logic clk,
    input logic reset,
    input logic cond1,
    input logic cond2,
    input logic [7:0] data_in,
    output logic [7:0] out_nested_a,
    output logic [7:0] out_nested_b
);
    logic [7:0] /* isolate_assignments */ split_nested_var;
    logic [7:0] other_nested_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_nested_var <= 8'b0;
            other_nested_var <= 8'b0;
        end else begin
            split_nested_var <= 8'h11; 
            other_nested_var <= 8'h22; 
            if (cond1) begin
                split_nested_var <= data_in + 10;
                other_nested_var <= data_in + 20;
                if (cond2) begin
                    split_nested_var <= data_in + 100;
                    other_nested_var <= data_in + 200;
                end
            end else begin
                split_nested_var <= data_in - 10;
                other_nested_var <= data_in - 20;
            end
        end
    end
    always_comb begin
        out_nested_a = split_nested_var;
        out_nested_b = other_nested_var;
    end
endmodule
module mod_split_func_call (
    input logic clk,
    input logic reset,
    input logic [7:0] data_in,
    output logic [7:0] out_func_a,
    output logic [7:0] out_func_b
);
    function automatic logic [7:0] dummy_func (input logic [7:0] val);
        return val + 5;
    endfunction
    logic [7:0] /* isolate_assignments */ split_func_var;
    logic [7:0] other_func_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_func_var <= 8'b0;
            other_func_var <= 8'b0;
        end else begin
            split_func_var <= dummy_func(data_in);
            other_func_var <= data_in + 1;
            if (data_in > 50) begin
                other_func_var <= dummy_func(data_in + 10);
            end
            out_func_a <= split_func_var;
            out_func_b <= other_func_var;
        end
    end
endmodule
