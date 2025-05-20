module sequential_register (
    input logic clk,
    input logic reset_n,
    input logic enable_in,
    input logic data_in,
    output logic data_out
);
    always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      data_out <= 1'b0; 
    end else if (enable_in) begin
      data_out <= data_in; 
    end
          2'b01: begin 
                   data_out_fmt = ~data_in_fmt; 
                 end 
          2'b10: begin 
                   logic [7:0] added_val; 
                   added_val = data_in_fmt + 8'h01; 
                   data_out_fmt = added_val; 
                 end 
          default: data_out_fmt = 8'hFF; 
        endcase 
      end else begin
        data_out_fmt = data_in_fmt - 8'h01; 
      end 
    end else begin
      data_out_fmt = 8'h00; 
    end 
      end
endmodule

