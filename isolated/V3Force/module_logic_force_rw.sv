module module_logic_force_rw (
    input wire i_clk,
    input logic i_data_in,
    input logic i_force_en,
    input logic i_force_val,
    input logic i_release_en,
    input wire i_rst_n,
    input logic i_write_en,
    output logic o_logic_target,
    output logic o_read_logic
);
    logic normal_l_target_reg;
    logic l_target;
    logic l_read_internal;
    assign o_logic_target = l_target;
    assign o_read_logic = l_read_internal;
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            normal_l_target_reg <= 1'b0;
            l_read_internal <= 1'b0;
        end else begin
            l_read_internal <= l_target;
            if (i_write_en) begin
                normal_l_target_reg <= i_data_in;
            end
        end
    end
    always_comb begin
        if (i_force_en) begin
            force l_target = i_force_val;
        end else if (i_release_en) begin
            release l_target;
        end else begin
            l_target = normal_l_target_reg;
        end
    end
endmodule

