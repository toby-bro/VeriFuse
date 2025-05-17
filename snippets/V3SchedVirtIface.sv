interface my_if;
  logic [7:0] data;
  logic ready;
  logic valid;
  modport FullAccess (input data, output ready, output valid);
  modport AccessIn (output data, output valid, input ready);
  modport AccessOut (input data, input valid, output ready);
endinterface
interface cond_if;
  logic [15:0] control_reg;
  logic [15:0] status_reg;
  modport CtrlStat (output control_reg, input status_reg);
endinterface
interface loop_if;
  logic [3:0] index;
  logic done;
  modport Ctrl (output index, output done);
  modport Report (input index, input done);
endinterface
interface seq_if;
  logic [31:0] value_a;
  modport PortA (output value_a);
endinterface
interface seq2_if;
  logic [7:0] status_byte;
  modport PortB (output status_byte);
endinterface
interface struct_if;
  logic [7:0] packet_field1;
  logic [7:0] packet_field2;
  logic tx_en;
  modport Access (output packet_field1, output packet_field2, output tx_en);
endinterface
module module_assign_blocking(
    input logic [7:0] in_data,
    output logic out_valid_status
);
  my_if vif_inst();
  always_comb begin
    vif_inst.data = in_data;
    vif_inst.valid = 1'b1;
    vif_inst.ready = 1'b0;
    out_valid_status = vif_inst.valid;
  end
endmodule
module module_assign_nonblocking(
    input logic clk,
    input logic reset,
    input logic [7:0] in_value,
    output logic out_data_q
);
  my_if vif_inst();
  logic [7:0] data_q;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      vif_inst.data <= 8'h0;
      data_q <= 8'h0;
    end else begin
      vif_inst.data <= in_value;
      data_q <= vif_inst.data;
    end
  end
  assign out_data_q = data_q;
endmodule
module module_sequential_writes(
    input logic [7:0] addr,
    input logic [7:0] wdata,
    output logic write_status
);
  my_if vif_bus();
  always_comb begin
    vif_bus.data = wdata;
    vif_bus.ready = 1'b1;
    vif_bus.valid = 1'b0;
    write_status = vif_bus.ready;
  end
endmodule
module module_conditional_write(
    input logic condition,
    input logic [15:0] data_in,
    output logic control_status
);
  cond_if cif_inst();
  always_comb begin
    if (condition) begin
      cif_inst.control_reg = data_in;
    end else begin
      cif_inst.control_reg = 16'h0;
    end
    control_status = (cif_inst.control_reg != 16'h0);
  end
endmodule
module module_while_write(
    input logic enable_loop,
    input logic [3:0] start_index,
    output logic loop_active
);
  loop_if lif_inst();
  always_comb begin
    logic [3:0] i_local;
    i_local = 4'h0;
    loop_active = 1'b0;
    lif_inst.index = start_index;
    lif_inst.done = 1'b1;
    if (enable_loop) begin
      i_local = start_index;
      while (i_local < 10) begin
        lif_inst.index = i_local;
        lif_inst.done = 1'b0;
        i_local = i_local + 1;
        loop_active = 1'b1;
      end
      lif_inst.done = (i_local == 10);
    end else begin
      loop_active = 1'b0;
    end
  end
endmodule
module module_for_write(
    input logic enable_for,
    input logic [3:0] limit,
    output logic for_completed
);
  loop_if lif_for();
  always_comb begin
    logic [3:0] i;
    for_completed = 1'b0;
    lif_for.index = 4'h0;
    lif_for.done = 1'b0;
    if (enable_for) begin
      for (i = 0; i < limit; i = i + 1) begin
        lif_for.index = i;
        lif_for.done = 1'b0;
      end
      lif_for.done = 1'b1;
      for_completed = 1'b1;
    end else begin
        for_completed = 1'b0;
    end
  end
endmodule
module module_sequence_different_if(
    input logic [31:0] input1,
    input logic [7:0] input2_byte,
    output logic sequence_valid
);
  seq_if sif_port();
  seq2_if sif2_port();
  always_comb begin
    sif_port.value_a = input1;
    sif2_port.status_byte = input2_byte;
    sequence_valid = 1'b1;
  end
endmodule
module module_struct_write(
    input logic [7:0] in_field1,
    input logic [7:0] in_field2,
    output logic tx_status
);
  struct_if stif_inst();
  always_comb begin
    stif_inst.packet_field1 = in_field1;
    stif_inst.packet_field2 = in_field2;
    stif_inst.tx_en = 1'b1;
    tx_status = stif_inst.tx_en;
  end
endmodule
module module_fork_join(
    input logic fork_en,
    input logic [7:0] data_a,
    input logic [7:0] data_b,
    output logic fork_status
);
  my_if vif_split();
  always_comb begin
    fork_status = 1'b0;
    vif_split.data = 8'h0;
    vif_split.ready = 1'b0;
    vif_split.valid = 1'b0;
    if (fork_en) begin
      fork
        vif_split.data = data_a;
        vif_split.ready = 1'b1;
      join_none
      fork_status = 1'b1;
    end else begin
        fork_status = 1'b0;
    end
  end
endmodule
module module_task_write(
    input logic task_en,
    input logic [7:0] in_task_data,
    output logic task_output_valid
);
  my_if task_vif_inst();
  task automatic update_vif_signals(input logic en, input logic [7:0] data_val,
                                    output logic [7:0] vif_data, output logic vif_valid, output logic vif_ready);
    if (en) begin
      vif_data = data_val;
      vif_valid = 1'b1;
      vif_ready = 1'b0;
    end else begin
      vif_data = 8'h0;
      vif_valid = 1'b0;
      vif_ready = 1'b1;
    end
  endtask
  always_comb begin
    update_vif_signals(task_en, in_task_data, task_vif_inst.data, task_vif_inst.valid, task_vif_inst.ready);
    task_output_valid = task_vif_inst.valid;
  end
endmodule
module module_case_write(
    input logic [1:0] select_case,
    input logic [7:0] data_case_a,
    input logic [7:0] data_case_b,
    output logic case_output_ready
);
  my_if case_vif_inst();
  always_comb begin
    case (select_case)
      2'b00: begin
        case_vif_inst.data = 8'hAA;
        case_vif_inst.valid = 1'b1;
        case_vif_inst.ready = 1'b0;
      end
      2'b01: begin
        case_vif_inst.data = data_case_a;
        case_vif_inst.valid = 1'b0;
        case_vif_inst.ready = 1'b1;
      end
      2'b10: begin
        case_vif_inst.data = data_case_b;
        case_vif_inst.valid = 1'b1;
        case_vif_inst.ready = 1'b1;
      end
      default: begin
        case_vif_inst.data = 8'hFF;
        case_vif_inst.valid = 1'b0;
        case_vif_inst.ready = 1'b0;
      end
    endcase
    case_output_ready = case_vif_inst.ready;
  end
endmodule
