module module_logic_force_cont_read (
    input logic i_data_in,
    input logic i_force_val,
    input logic i_force_en,
    input logic i_release_en,
    output logic o_simple_read,
    input wire i_clk,
    input wire i_rst_n
);
    logic normal_l_simple_target_reg;
    logic l_simple_target;
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            normal_l_simple_target_reg <= 1'b0;
        end else begin
            normal_l_simple_target_reg <= i_data_in;
        end
    end
    always_comb begin
        if (i_force_en) begin
            force l_simple_target = i_force_val;
        end else if (i_release_en) begin
            release l_simple_target;
        end else begin
            l_simple_target = normal_l_simple_target_reg;
        end
    end
    assign o_simple_read = l_simple_target;
endmodule

