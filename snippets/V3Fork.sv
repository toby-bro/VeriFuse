class MyClass;
  int val = 1;
  function new();
    val = 0;
  endfunction
  function void set_val(int v);
    val = v;
  endfunction
  function int get_val();
    return val;
  endfunction
endclass
module ModuleForkJoinNoneBasic(
  input bit clk,
  input int in_a,
  input int in_b,
  output logic [31:0] out_sum
);
  always @(posedge clk) begin automatic
    automatic int local_var_sum = in_a;
    automatic int parent_in_b = in_b;
    fork : my_fork_none_sum
      @(negedge clk);
      local_var_sum = local_var_sum + parent_in_b;
    join_none
    out_sum = local_var_sum;
  end
endmodule
module ModuleForkJoinAnyBasic(
  input bit clk,
  input int in_c,
  input int in_d,
  output logic [31:0] out_prod
);
  always @(posedge clk) begin automatic
    automatic int local_prod_parent = in_c;
    automatic int parent_in_d = in_d;
    fork : my_fork_any_prod
      @(negedge clk);
      local_prod_parent = local_prod_parent * parent_in_d;
    join_any
    out_prod = local_prod_parent;
  end
endmodule
module ModuleForkJoinBasic(
  input bit clk,
  input int in_e,
  input int in_f,
  output logic [31:0] out_total
);
  always @(posedge clk) begin automatic
    automatic int local_val1_parent = in_e;
    automatic int local_val2_parent = in_f;
    fork : my_fork_join
      begin : process1
        @(negedge clk);
        local_val1_parent = local_val1_parent + 1;
      end
      begin : process2
        @(posedge clk);
        local_val2_parent = local_val2_parent - 1;
      end
    join
    out_total = local_val1_parent + local_val2_parent;
  end
endmodule
module ModuleForkBeginBlock(
  input bit clk,
  input int in_x,
  output logic [31:0] out_y
);
  always @(posedge clk) begin automatic
    automatic int parent_local_var = in_x;
    fork : fork_with_begin
      begin : my_begin_block
        @(negedge clk);
        parent_local_var = parent_local_var + 10;
      end
    join_none
    out_y = parent_local_var * 2;
  end
endmodule
module ModuleForkClassHandle(
  input bit clk,
  input int in_obj_val,
  output logic [31:0] out_obj_val
);
  always @(posedge clk) begin automatic
    automatic MyClass my_handle = null;
    if (my_handle == null) begin
      my_handle = new();
    end
    my_handle.set_val(in_obj_val);
    fork : fork_with_class
      @(negedge clk);
      my_handle.set_val(my_handle.get_val() + 5);
    join_none
    out_obj_val = my_handle.get_val();
  end
endmodule
module ModuleForkMultiProcess(
  input bit clk,
  input int in_m1,
  input int in_m2,
  output logic [31:0] out_m_res
);
  always @(posedge clk) begin automatic
    automatic int v1_parent = in_m1;
    automatic int v2_parent = in_m2;
    fork : multi_process_fork
      begin : process1
        @(negedge clk);
        v1_parent = v1_parent + 1;
      end
      begin : process2
        @(posedge clk);
        v2_parent = v2_parent * 2;
      end
    join_none
    out_m_res = v1_parent + v2_parent;
  end
endmodule
module ModuleForkAssignDly(
  input bit clk,
  input int in_val,
  output logic [31:0] out_q
);
  always @(posedge clk) begin automatic
    automatic int local_auto_var = in_val;
    @(negedge clk) local_auto_var <= local_auto_var + 5;
    out_q = local_auto_var;
  end
endmodule
module ModuleForkNested(
  input bit clk,
  input int in_n,
  output logic [31:0] out_n
);
  always @(posedge clk) begin automatic
    automatic int outer_local_parent = in_n;
    fork : outer_fork
      @(negedge clk);
      fork : inner_fork
        @(posedge clk);
        outer_local_parent = outer_local_parent * 3;
      join_none
    join_none
    out_n = outer_local_parent;
  end
endmodule
module ModuleForkEvent(
  input bit clk,
  input bit in_trigger,
  output logic [31:0] out_event_status
);
  event ev;
  always @(posedge clk) begin automatic
    automatic logic [31:0] local_status_parent = 0;
    if (in_trigger) begin
      -> ev;
      local_status_parent = 1;
    end
    fork : event_fork
      @(ev);
      local_status_parent = local_status_parent + 10;
    join_none
    out_event_status = local_status_parent;
  end
endmodule
module ModuleForkHeaderBlockItems(
  input bit clk,
  input int in_h1,
  input int in_h2,
  output logic [31:0] out_h_res
);
  always @(posedge clk) begin automatic
    fork : header_fork
      automatic int header_var = in_h1;
      automatic logic [31:0] temp_val = in_h2;
      begin
        @(negedge clk);
        out_h_res = header_var + temp_val;
      end
    join
  end
endmodule
module ModuleForkMultipleAutomaticVars(
  input bit clk,
  input int in_m_a,
  input int in_m_b,
  output logic [31:0] out_m_res1
);
  always @(posedge clk) begin automatic
    automatic int var_a_parent = in_m_a;
    automatic int var_b_parent = 0;
    fork : multiple_vars_fork
      automatic int fork_local_a = var_a_parent;
      automatic int fork_local_b_init = in_m_b;
      @(negedge clk);
      var_a_parent = fork_local_a + 1;
      var_b_parent = fork_local_b_init * 2;
    join_none
    out_m_res1 = var_a_parent + var_b_parent;
  end
endmodule
module ModuleReadOnlyAfterTimingControl(
  input bit clk,
  input int in_data,
  output logic [31:0] out_data_plus
);
  always @(posedge clk) begin automatic
    automatic int local_read_only_parent = in_data;
    fork : read_only_fork
      @(negedge clk);
      out_data_plus = local_read_only_parent + 1;
    join_none
  end
endmodule
module ModuleForkMultiSuspend(
  input bit clk,
  input int in_ms,
  output logic [31:0] out_ms
);
  always @(posedge clk) begin automatic
    automatic int local_ms_parent = in_ms;
    fork : multi_suspend_fork
      @(negedge clk);
      local_ms_parent = local_ms_parent + 10;
      @(posedge clk);
      local_ms_parent = local_ms_parent * 2;
    join_none
    out_ms = local_ms_parent;
  end
endmodule
module ModuleForkMultiAccess(
  input bit clk,
  input int in_val,
  output logic [31:0] out_res
);
  always @(posedge clk) begin automatic
    automatic int parent_var = in_val;
    fork : multi_access_fork
      begin : process_A
        @(negedge clk);
        parent_var = parent_var + 1;
      end
      begin : process_B
        @(posedge clk);
        parent_var = parent_var * 2;
      end
    join_none
    out_res = parent_var;
  end
endmodule
module ModuleTaskWithFork(
  input bit clk,
  input int in_task_val,
  output logic [31:0] out_task_res
);
  task automatic my_async_task;
    input int task_input;
    inout int task_inout_var;
    automatic int task_local_var = task_input;
    fork : task_inner_fork
      @(negedge clk);
      task_local_var = task_local_var + 100;
      task_inout_var = task_local_var;
    join_none
  endtask
  always @(posedge clk) automatic begin : clocked_process_auto
    automatic int local_var_in_always = in_task_val;
    my_async_task(in_task_val + 1, local_var_in_always);
    out_task_res = local_var_in_always;
  end
endmodule
module ModuleTaskWithInoutFork(
  input bit clk,
  input int in_task_val_inout,
  output logic [31:0] out_task_inout_res
);
  task automatic my_inout_task;
    input int task_input;
    inout int task_inout_arg;
    automatic int task_local_var = task_input;
    fork : task_inner_fork_inout
      @(negedge clk);
      task_local_var = task_local_var + 100;
      task_inout_arg = task_inout_arg * 2;
    join_none
  endtask
  always @(posedge clk) automatic begin : clocked_process_auto_inout
    automatic int local_var_to_pass_as_inout = in_task_val_inout;
    my_inout_task(in_task_val_inout + 1, local_var_to_pass_as_inout);
    out_task_inout_res = local_var_to_pass_as_inout;
  end
endmodule
module ModuleForkHeaderAssign(
  input bit clk,
  input int in_a,
  input int in_b,
  output logic [31:0] out_res
);
  always @(posedge clk) begin automatic
    automatic int parent_var = in_a;
    fork : header_assign_fork
      automatic int header_var = in_b;
      parent_var = header_var + 10;
      begin
        @(negedge clk);
        out_res = parent_var;
      end
    join_none
  end
endmodule
module ModuleFuncCallInFork(
  input bit clk,
  input int in_func_val,
  output logic [31:0] out_func_res
);
  function automatic int my_simple_func(input int val);
    return val * 2;
  endfunction
  always @(posedge clk) begin automatic
    automatic int parent_func_var = in_func_val;
    fork : func_call_fork
      @(negedge clk);
      parent_func_var = my_simple_func(parent_func_var);
    join_none
    out_func_res = parent_func_var + 1;
  end
endmodule
