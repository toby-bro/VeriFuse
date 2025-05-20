module formatting_stress (
    output logic [7:0] data_out_fmt,
    input logic [7:0] data_in_fmt,
    input logic sel_fmt,
    input logic enable_block_fmt,
    input logic [1:0] case_sel_fmt
);
    logic [7:0] temp_reg_fmt; 
      always_comb begin : stress_comb_block_label 
    data_out_fmt = 8'hXX; 
    if (enable_block_fmt) begin
      if (sel_fmt) begin
        case (case_sel_fmt) 
          2'b00: data_out_fmt = data_in_fmt;
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

