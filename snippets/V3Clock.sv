module ModClockedReg (
    input clk,
    input d,
    output logic q
);
always @(posedge clk) begin
    q <= d;
end
endmodule
module ModClockedResetReg (
    input clk,
    input rst_n,
    input d,
    output logic q
);
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        q <= 1'b0;
    end else begin
        q <= d;
    end
end
endmodule
module ModClockedConditional (
    input clk,
    input enable,
    input data_in,
    output logic data_out
);
logic reg_data;
always @(posedge clk) begin
    if (enable) begin
        reg_data <= data_in;
    end
end
assign data_out = reg_data;
endmodule
module ModSampledVarLogic (
    input clk,
    input [3:0] data_in,
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
module ModMultipleAlways (
    input clk_a,
    input clk_b,
    input rst_n,
    input din_a,
    input din_b,
    output logic dout_a,
    output logic dout_b
);
always @(posedge clk_a or negedge rst_n) begin 
    if (!rst_n) begin 
        dout_a <= 1'b0;
    end else begin
        dout_a <= din_a; 
    end
end
always @(posedge clk_b) begin 
    dout_b <= din_b; 
end
endmodule
module ModClockedWithSimpleAssign (
    input clk,
    input in_a,
    input in_b,
    output logic out_comb,
    output logic out_reg
);
logic internal_reg;
always @(posedge clk) begin 
    internal_reg <= in_a; 
end
assign out_comb = in_a ^ in_b; 
always @(posedge clk) begin 
    out_reg <= internal_reg & in_b; 
end
endmodule
