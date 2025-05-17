module assert_property_mod(
    input logic clk,
    input logic data_in,
    output logic prop_out
);
  property p_data_simple_concurrent;
    @(posedge clk) data_in;
  endproperty
  assert property (p_data_simple_concurrent);
  always @(posedge clk) begin
    assert (data_in);
  end
  assign prop_out = data_in;
endmodule
module cover_property_mod(
    input logic clk,
    input logic cover_cond,
    output logic cover_out
);
  property p_cover_simple_concurrent;
    @(posedge clk) cover_cond;
  endproperty
  cover property (p_cover_simple_concurrent);
  always @(posedge clk) begin
    cover (cover_cond);
  end
  assign cover_out = cover_cond;
endmodule
module assume_property_mod(
    input logic clk,
    input logic assume_cond,
    output logic assume_out
);
  property p_assume_simple_concurrent;
    @(posedge clk) assume_cond;
  endproperty
  assume property (p_assume_simple_concurrent);
  always @(posedge clk) begin
    assume (assume_cond);
  end
  assign assume_out = assume_cond;
endmodule
module restrict_property_mod(
    input logic clk,
    input logic restrict_cond,
    output logic restrict_out
);
  property p_restrict_simple_concurrent;
    @(posedge clk) restrict_cond;
  endproperty
  restrict property (p_restrict_simple_concurrent);
  assign restrict_out = restrict_cond;
endmodule
module sampled_past_mod(
    input logic clk,
    input logic reset,
    input logic [3:0] data_in,
    output logic [3:0] data_past_out,
    output logic [3:0] data_sampled_out
);
  logic [3:0] past_internal;
  always @(posedge clk) begin
    past_internal <= $past(data_in, 2);
  end
  assign data_past_out = past_internal;
  assign data_sampled_out = $sampled(data_in);
endmodule
module assert_control_mod(
    input logic clk,
    input logic [1:0] trigger,
    output logic ctrl_out
);
  always @(posedge clk) begin
    if (trigger == 2'b01) begin
      $asserton(1, 1);
    end else if (trigger == 2'b10) begin
      $assertoff(2, 2);
    end else if (trigger == 2'b11) begin
      $assertkill(4, 4);
    end
  end
  assign ctrl_out = trigger[0];
endmodule
module display_tasks_mod(
    input logic trigger_disp,
    output logic disp_out
);
  always @(trigger_disp) begin
    if (trigger_disp) begin
      $info("This is an info message");
      $warning("This is a warning message");
      $error("This is an error message");
      $fatal(1, "This is a fatal message");
      $display("This is a display message");
      $write("This is a write message\n");
    end
  end
  assign disp_out = trigger_disp;
endmodule
module monitor_mod(
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
module monitoroff_mod(
    input logic trigger_monoff,
    output logic monoff_out
);
  always @(trigger_monoff) begin
    if (trigger_monoff) begin
      $monitoroff;
    end
  end
  assign monoff_out = trigger_monoff;
endmodule
module strobe_mod(
    input logic trigger_strobe,
    output logic strobe_out
);
  always @(trigger_strobe) begin
    if (trigger_strobe) begin
      $strobe("This is a strobe message");
    end
  end
  assign strobe_out = trigger_strobe;
endmodule
module if_pragmas_mod(
    input logic sel1,
    input logic sel2,
    input logic sel3,
    output logic if_pragma_out
);
  logic internal_out = 0;
  always @* begin
    internal_out = 0;
    (* unique *)
    if (sel1) begin
      internal_out = 1;
    end else if (sel2) begin
      internal_out = 2;
    end else begin
      internal_out = 3;
    end
    (* unique0 *)
    if (sel1 && sel2) begin
      internal_out = 4;
    end else if (sel2 && sel3) begin
      internal_out = 5;
    end
  end
  assign if_pragma_out = internal_out;
endmodule
module case_pragmas_mod(
    input logic [1:0] case_expr,
    input logic [3:0] case_inside_val,
    input logic [3:0] range_start,
    input logic [3:0] range_end,
    output logic case_pragma_out
);
  logic [4:0] internal_out = 0;
  always @* begin
    internal_out = 0;
    (* full, parallel *)
    case (case_expr)
      2'b00: internal_out = 1;
      2'b01: internal_out = 2;
      2'b10: internal_out = 3;
      default: internal_out = 4;
    endcase
    (* unique, priority *)
    casez (case_expr)
      2'b1?: internal_out = 5;
      2'b0?: internal_out = 6;
      default: internal_out = 7;
    endcase
    (* unique0 *)
    casez (case_expr)
      2'b1?: internal_out = 8;
      2'b0?: internal_out = 9;
    endcase
    (* full *)
    case (case_expr)
      2'b00: internal_out = 10;
      2'b01: internal_out = 11;
      2'b10: internal_out = 12;
      default: internal_out = 13;
    endcase
    (* parallel *)
    case (case_inside_val)
      4'd0, 4'd1: internal_out = 14;
      4'd2, 4'd3: internal_out = 15;
      default: internal_out = 18;
    endcase
    (* unique *)
    case (case_inside_val)
      case_inside_val inside {[range_start:range_end]}: internal_out = 16;
      case_inside_val inside {8}: internal_out = 17;
      default: internal_out = 18;
    endcase
    (* unique0 *)
    case (case_inside_val)
       case_inside_val inside {4'd10, 4'd11}: internal_out = 19;
       case_inside_val inside {4'd12}: internal_out = 20;
    endcase
  end
  assign case_pragma_out = internal_out;
endmodule
module procedural_assert_mod(
    input logic clk,
    input logic proc_cond,
    output logic proc_assert_out
);
  always @(posedge clk) begin
    assert (proc_cond) else $error("Procedural assertion failed");
    assert (1'b0);
  end
  assign proc_assert_out = proc_cond;
endmodule
