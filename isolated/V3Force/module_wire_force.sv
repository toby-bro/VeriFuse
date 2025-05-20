module module_wire_force (
    input wire i_rst_n,
    input wire i_data_in,
    input wire i_force_val,
    input logic i_force_en,
    input logic i_release_en,
    output logic o_wire_target,
    input wire i_clk
);
    logic normal_w_target_reg;
    logic w_target;
    assign o_wire_target = w_target;
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            normal_w_target_reg <= 1'b0;
        end else begin
            normal_w_target_reg <= i_data_in;
        end
    end
    always_comb begin
        if (i_force_en) begin
            force w_target = i_force_val;
        end else if (i_release_en) begin
            release w_target;
        end else begin
            w_target = normal_w_target_reg;
        end
    end
endmodule

