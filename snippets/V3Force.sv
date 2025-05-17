class MyDataClass;
    logic [15:0] data;
    function new(int initial_val);
        data = initial_val;
    endfunction
endclass
module module_wire_force (
    input wire i_clk,
    input wire i_rst_n,
    input wire i_data_in,
    input wire i_force_val,
    input logic i_force_en,
    input logic i_release_en,
    output logic o_wire_target
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
module module_logic_force_rw (
    input wire i_clk,
    input wire i_rst_n,
    input logic i_force_val,
    input logic i_force_en,
    input logic i_release_en,
    input logic i_data_in,
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
module module_bus_force_rw (
    input wire i_clk,
    input wire i_rst_n,
    input logic [7:0] i_force_val_bus,
    input logic i_force_en,
    input logic i_release_en,
    input logic [7:0] i_data_in_bus,
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
module module_logic_force_cont_read (
    input wire i_clk,
    input wire i_rst_n,
    input logic i_data_in,
    input logic i_force_val,
    input logic i_force_en,
    input logic i_release_en,
    output logic o_simple_read
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
module module_sv_class (
    input wire i_clk,
    input wire i_enable_create,
    output logic [15:0] o_class_data
);
    MyDataClass my_object = null;
    logic [15:0] stored_data;
    assign o_class_data = stored_data;
    always @(posedge i_clk) begin
        if (i_enable_create && my_object == null) begin
            /* verilator lint_off BLKSEQ */ my_object = new(123); /* verilator lint_on BLKSEQ */
        end
        if (my_object != null) begin
            stored_data <= my_object.data;
        end else begin
            stored_data <= 16'b0;
        end
    end
endmodule
module module_forceable_attr (
    input wire i_clk,
    input wire i_rst_n,
    input logic i_data_in,
    input logic i_write_en,
    output logic o_forceable_signal,
    output logic o_read_signal
);
    logic forceable_signal /* verilator public */;
    logic read_internal;
    assign o_forceable_signal = forceable_signal;
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            forceable_signal <= 1'b0;
            read_internal <= 1'b0;
        end else begin
            if (i_write_en) begin
                 forceable_signal <= i_data_in;
            end
            read_internal <= forceable_signal;
        end
    end
    assign o_read_signal = read_internal;
endmodule
module module_force_rhs_write (
    input wire i_clk,
    input wire i_rst_n,
    input logic i_data_for_rhs,
    input logic i_force_en,
    input logic i_release_en,
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
