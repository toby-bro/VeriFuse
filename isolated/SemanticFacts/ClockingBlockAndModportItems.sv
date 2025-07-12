module ClockingBlockAndModportItems (
    input logic clk_cb,
    input logic [7:0] data_in_cb,
    input logic internal_sig_cb_in,
    input logic rst_cb,
    output logic [7:0] data_out_cb
);
    logic [3:0] internal_data_cb;
    logic [3:0] cb_input_data;
    logic       cb_output_sig;
    logic [3:0] cb_output_data;
    logic       internal_sig_derived;
    assign internal_sig_derived = data_in_cb[7] | internal_sig_cb_in;
    assign cb_input_data        = data_in_cb[3:0];
    clocking cb @(posedge clk_cb);
        input  cb_input_data;
        input  internal_sig_derived;
        output cb_output_data;
        output cb_output_sig;
    endclocking
    always @(posedge clk_cb) begin
        internal_data_cb  = cb_input_data + (internal_sig_derived ? 1 : 0);
        cb_output_data   <= internal_data_cb;
        cb_output_sig    <= internal_data_cb[0];
    end
    assign data_out_cb = {4'b0000, cb_output_data};
endmodule

