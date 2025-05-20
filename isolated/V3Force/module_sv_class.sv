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
            ;
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

