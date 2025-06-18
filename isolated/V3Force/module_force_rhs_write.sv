module module_force_rhs_write (
    input wire i_clk,
    input logic i_data_for_rhs,
    input logic i_force_en,
    input logic i_release_en,
    input wire i_rst_n,
    output logic o_force_target,
    output logic o_rhs_signal_read
);
    logic force_target;
    logic rhs_signal;
    logic rhs_signal_reg;
    assign o_force_target = force_target;
    assign o_rhs_signal_read = rhs_signal_reg;
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            rhs_signal_reg <= 1'b0;
        end else begin
            rhs_signal_reg <= i_data_for_rhs;
        end
    end
    assign rhs_signal = rhs_signal_reg;
    always_comb begin
        if (i_force_en) begin
            force force_target = rhs_signal;
        end else if (i_release_en) begin
            release force_target;
        end else begin
            force_target = 1'b0;
        end
    end
endmodule

