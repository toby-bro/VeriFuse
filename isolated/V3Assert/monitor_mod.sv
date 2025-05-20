module monitor_mod (
    input logic clk,
    input logic [7:0] mon_data1,
    input logic [7:0] mon_data2,
    output logic mon_out
);
    always @(posedge clk) begin
    $monitor("Monitor: data1=%h, data2=%h", mon_data1, mon_data2);
      end
      assign mon_out = mon_data1[0] | mon_data2[0];
endmodule

