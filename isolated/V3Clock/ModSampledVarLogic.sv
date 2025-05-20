module ModSampledVarLogic (
    input logic clk,
    input logic [3:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] __Vsampled_state = 8'hAB; 
    logic [7:0] internal_reg;
    always @(posedge clk) begin
    if (data_in == 4'd5) begin 
        internal_reg <= __Vsampled_state + data_in; 
    end else if (data_in > 4'd8) begin 
        internal_reg <= {4'h0, data_in} - 1; 
    end else begin
        internal_reg <= 8'hFF;
    end
    end
    assign data_out = internal_reg;
endmodule

