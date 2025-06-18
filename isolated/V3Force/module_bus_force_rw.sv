module module_bus_force_rw (
    input wire i_clk,
    input logic [7:0] i_data_in_bus,
    input logic i_force_en,
    input logic [7:0] i_force_val_bus,
    input logic i_release_en,
    input wire i_rst_n,
    input logic i_write_en,
    output logic [7:0] o_logic_bus_target,
    output logic [7:0] o_read_logic_bus
);
    logic [7:0] normal_l_bus_target_reg;
    logic [7:0] l_bus_target;
    logic [7:0] l_bus_read_internal;
    assign o_logic_bus_target = l_bus_target;
    assign o_read_logic_bus = l_bus_read_internal;
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            normal_l_bus_target_reg <= 8'b0;
            l_bus_read_internal <= 8'b0;
        end else begin
            l_bus_read_internal <= l_bus_target;
            if (i_write_en) begin
                normal_l_bus_target_reg <= i_data_in_bus;
            end
        end
    end
    always_comb begin
        if (i_force_en) begin
            force l_bus_target = i_force_val_bus;
        end else if (i_release_en) begin
            release l_bus_target;
        end else begin
            l_bus_target = normal_l_bus_target_reg;
        end
    end
endmodule

