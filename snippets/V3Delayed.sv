module mod_shadow_var (
  input logic clk,
  input logic reset,
  input logic [7:0] in_data,
  output logic [7:0] out_reg
);
logic [7:0] internal_reg;
always @(posedge clk or posedge reset) begin
  if (reset) begin
    internal_reg <= 8'h00;
  end else begin
    internal_reg <= in_data;
  end
end
assign out_reg = internal_reg;
endmodule
module mod_flag_shared (
  input logic clk,
  input logic reset,
  input logic [3:0] index,
  input logic [7:0] in_val,
  output logic [7:0] out_element
);
logic [7:0] data_array [16];
integer i;
always_ff @(posedge clk or posedge reset) begin
  if (reset) begin
    for (i=0; i<16; i=i+1) data_array[i] = 8'h00;
  end else begin
    data_array[index] <= in_val;
  end
end
assign out_element = data_array[index];
endmodule
module mod_flag_shared_consecutive (
  input logic clk,
  input logic reset,
  input logic [3:0] index1,
  input logic [3:0] index2,
  input logic [7:0] in_val1,
  input logic [7:0] in_val2,
  output logic [7:0] out_element1,
  output logic [7:0] out_element2
);
logic [7:0] data_array [16];
integer i;
always_ff @(posedge clk or posedge reset) begin
  if (reset) begin
      for (i=0; i<16; i=i+1) data_array[i] = 8'h00;
  end else begin
    data_array[index1] <= in_val1;
    data_array[index2] <= in_val2;
  end
end
assign out_element1 = data_array[index1];
assign out_element2 = data_array[index2];
endmodule
module mod_flag_unique_fork (
  input logic clk,
  input logic reset,
  input logic trigger,
  input logic [7:0] in_val,
  output logic [7:0] out_reg
);
logic [7:0] fork_reg;
always @(posedge clk or posedge reset) begin
  if (reset) begin
    fork_reg <= 8'h00;
  end else begin
    if (trigger) begin
      fork
        fork_reg <= in_val;
      join_none
    end
  end
end
assign out_reg = fork_reg;
endmodule
module mod_value_queue_whole_loop (
  input logic clk,
  input logic reset,
  input logic start_loop,
  input logic [7:0] data_in,
  input logic [2:0] base_index,
  output logic [7:0] data_out_element
);
logic [7:0] queue_array [16];
integer i;
always @(posedge clk or posedge reset) begin
  if (reset) begin
    for (i=0; i<16; i=i+1) queue_array[i] = 8'h00;
  end else begin
    if (start_loop) begin
      i = 0;
      while (i < 8) begin
        queue_array[base_index + i] <= data_in + i;
        i = i + 1;
      end
    end
  end
end
assign data_out_element = queue_array[base_index];
endmodule
module mod_value_queue_partial_loop (
  input logic clk,
  input logic reset,
  input logic start_loop,
  input logic [3:0] data_part,
  input logic [2:0] array_idx,
  input logic [1:0] part_lsb,
  output logic [7:0] output_array_element
);
logic [7:0] unpacked_array [16];
integer i;
always @(posedge clk or posedge reset) begin
  if (reset) begin
    for (i=0; i<16; i=i+1) unpacked_array[i] = 8'h00;
  end else begin
    if (start_loop) begin
      i = 0;
      while (i < 8) begin
        unpacked_array[array_idx + i][part_lsb + 4 +: 4] <= data_part + i;
        i = i + 1;
      end
    end
  end
end
assign output_array_element = unpacked_array[array_idx];
endmodule
module mod_unsupported_compound_loop (
  input logic clk,
  input logic reset,
  input logic start_loop,
  input logic [7:0] data_val,
  input logic [2:0] array_idx,
  output logic [15:0] output_struct_field2
);
typedef struct packed {
  logic [7:0] field1;
  logic [15:0] field2;
} my_struct_t;
my_struct_t struct_array [16];
integer i;
always @(posedge clk or posedge reset) begin
  if (reset) begin
    for (i=0; i<16; i=i+1) struct_array[i] = '{field1: 8'h00, field2: 16'h0000};
  end else begin
    if (start_loop) begin
      i = 0;
      while (i < 8) begin
        struct_array[array_idx + i] <= '{field1: data_val + i, field2: {8'h00, data_val} + i};
        i = i + 1;
      end
    end
  end
end
assign output_struct_field2 = struct_array[array_idx].field2;
endmodule
module mod_mixed_assignments (
  input logic clk,
  input logic reset,
  input logic [7:0] in_a,
  input logic [7:0] in_b,
  input logic en_blk,
  input logic en_nblk,
  output logic [7:0] mixed_reg_out
);
logic [7:0] shared_reg;
always @(posedge clk or posedge reset) begin
  if (reset) begin
    shared_reg <= 8'h00;
  end else begin
    if (en_blk) begin
      shared_reg = in_a;
    end
    if (en_nblk) begin
      shared_reg <= in_b;
    end
  end
end
assign mixed_reg_out = shared_reg;
endmodule
module mod_multidriven (
  input logic clk1,
  input logic reset1,
  input logic clk2,
  input logic reset2,
  input logic [7:0] in_val1,
  input logic [7:0] in_val2,
  output logic [7:0] multi_reg_out
);
logic [7:0] multi_reg;
always @(posedge clk1 or posedge reset1) begin
  if (reset1) begin
    multi_reg <= 8'h00;
  end else begin
    multi_reg <= in_val1;
  end
end
always @(posedge clk2 or posedge reset2) begin
  if (reset2) begin
    multi_reg <= 8'h00;
  end else begin
    multi_reg <= in_val2;
  end
end
assign multi_reg_out = multi_reg;
endmodule
module mod_readmemh (
  input logic clk,
  input logic reset,
  input logic [3:0] addr,
  output logic [7:0] mem_out
);
  logic [7:0] my_memory [0:15];
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      $readmemh("dummy_mem_file.mem", my_memory);
    end
  end
  assign mem_out = my_memory[addr];
endmodule
module mod_event_fire_suspendable (
  input logic clk,
  input logic reset,
  input logic trigger,
  output logic event_fired
);
  event my_event;
  logic event_status_reg;
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      event_status_reg = 1'b0;
    end else begin
      if (trigger) begin
        fork
          -> my_event;
        join_none
      end
    end
  end
  always @(my_event) begin
    event_status_reg <= ~event_status_reg;
  end
  assign event_fired = event_status_reg;
endmodule
module mod_real_nba (
  input logic clk,
  input logic reset,
  input real in_real,
  output real out_real_reg
);
real real_reg;
always @(posedge clk or posedge reset) begin
  if (reset) begin
    real_reg <= 0.0;
  end else begin
    real_reg <= in_real;
  end
end
assign out_real_reg = real_reg;
endmodule
module mod_event_sensitivity (
  input logic trigger_event,
  input logic [7:0] data_in,
  output logic [7:0] event_reg_out
);
event event_trigger;
logic [7:0] event_reg;
always @(event_trigger) begin
  event_reg <= data_in;
end
always_comb begin
  if (trigger_event) -> event_trigger;
end
assign event_reg_out = event_reg;
endmodule
module mod_packed_array_shadow (
  input logic clk,
  input logic reset,
  input logic [3:0] index,
  input logic [7:0] in_val,
  output logic [7:0] out_element
);
logic [15:0][7:0] packed_mem;
integer i;
always_ff @(posedge clk or posedge reset) begin
  if (reset) begin
    for (i=0; i<16; i=i+1) packed_mem[i] = 8'h00;
  end else begin
    packed_mem[index] <= in_val;
  end
end
assign out_element = packed_mem[index];
endmodule
module mod_packed_part_select_shadow (
  input logic clk,
  input logic reset,
  input logic [3:0] index,
  input logic [1:0] part_lsb,
  input logic [3:0] in_part,
  output logic [7:0] out_element
);
logic [15:0][7:0] packed_mem;
integer i;
always_ff @(posedge clk or posedge reset) begin
  if (reset) begin
    for (i=0; i<16; i=i+1) packed_mem[i] = 8'h00;
  end else begin
    packed_mem[index][part_lsb +: 4] <= in_part;
  end
end
assign out_element = packed_mem[index][0];
endmodule
module mod_case_nba (
  input logic clk,
  input logic reset,
  input logic [1:0] sel,
  input logic [7:0] data_a,
  input logic [7:0] data_b,
  output logic [7:0] case_reg_out
);
logic [7:0] case_reg;
always @(posedge clk or posedge reset) begin
  if (reset) begin
    case_reg <= 8'h00;
  end else begin
    case (sel)
      2'b00: case_reg <= data_a;
      2'b01: case_reg <= data_b;
      default: case_reg <= 8'hFF;
    endcase
  end
end
assign case_reg_out = case_reg;
endmodule
