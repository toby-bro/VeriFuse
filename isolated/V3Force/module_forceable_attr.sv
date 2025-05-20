module module_forceable_attr (
    output logic o_read_signal,
    input wire i_clk,
    input wire i_rst_n,
    input logic i_data_in,
    input logic i_write_en,
    output logic o_forceable_signal
);
    logic forceable_signal ;
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

