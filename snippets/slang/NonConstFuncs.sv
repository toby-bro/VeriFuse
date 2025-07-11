module FileOps(
  input  integer fd_in,
  input  byte    char_in,
  input  integer offset_in,
  input  integer origin_in,
  input  string  string_in,
  input  bit     dummy_input,
  output integer fopen_out,
  output integer feof_out,
  output integer ferror_status_out,
  output string  ferror_string_out,
  output integer char_out,
  output integer ungetc_out,
  output integer ftell_out,
  output integer fseek_out,
  output integer rewind_status_out,
  output string  fgets_out,
  output integer fscanf_ret_out,
  output integer fscanf_int_out,
  output string  fscanf_string_out,
  output integer fread_int_ret_out,
  output integer fread_array_ret_out,
  output integer fread_array_start_ret_out,
  output integer fread_array_start_count_ret_out,
  output integer fread_array_empty_start_ret_out,
  output integer sscanf_ret_out,
  output integer sscanf_int_out,
  output string  sscanf_string_out,
  output integer fflush_status_out,
  output integer fclose_status_out,
  output bit     dummy_output
);
  always_comb begin
    automatic integer local_fd;
    automatic string  local_sbuf = "";
    automatic integer local_int_var = 0;
    automatic logic [7:0] local_array_var [10];
    automatic integer local_char;
    automatic integer local_ret;
    local_fd = $fopen("dummy_read.txt", "r");
    fopen_out = local_fd;
    if (local_fd != 0) begin
      feof_out = $feof(local_fd);
      local_ret = $ferror(local_fd, local_sbuf);
      ferror_status_out = local_ret;
      ferror_string_out = local_sbuf;
      local_char = $fgetc(local_fd);
      char_out = local_char;
      ungetc_out = $ungetc(char_in, local_fd);
      ftell_out = $ftell(local_fd);
      local_ret = $fseek(local_fd, offset_in, origin_in);
      fseek_out = local_ret;
      rewind_status_out = $rewind(local_fd);
      local_ret = $fgets(local_sbuf, local_fd);
      fgets_out = local_sbuf;
      local_ret = $fscanf(local_fd, "%d %s", fscanf_int_out, fscanf_string_out);
      fscanf_ret_out = local_ret;
      local_ret = $fread(local_int_var, local_fd);
      fread_int_ret_out = local_ret;
      local_ret = $fread(local_array_var, local_fd);
      fread_array_ret_out = local_ret;
      local_ret = $fread(local_array_var, local_fd, 5);
      fread_array_start_ret_out = local_ret;
      local_ret = $fread(local_array_var, local_fd, 5, 10);
      fread_array_start_count_ret_out = local_ret;
      local_ret = $fread(local_array_var, local_fd, , 10);
      fread_array_empty_start_ret_out = local_ret;
      $fflush();
      $fflush(local_fd);
      fflush_status_out = 99;
      $fclose(local_fd);
      fclose_status_out = 99;
    end
    else begin
      feof_out = -1;
      ferror_status_out = -1;
      ferror_string_out = "File open failed";
      char_out = -1;
      ungetc_out = -1;
      ftell_out = -1;
      fseek_out = -1;
      rewind_status_out = -1;
      fgets_out = "";
      fscanf_ret_out = -1;
      fscanf_int_out = 0;
      fscanf_string_out = "";
      fread_int_ret_out = -1;
      fread_array_ret_out = -1;
      fread_array_start_ret_out = -1;
      fread_array_start_count_ret_out = -1;
      fread_array_empty_start_ret_out = -1;
      fflush_status_out = -1;
      fclose_status_out = -1;
    end
    local_ret = $sscanf(string_in, "%d %s", sscanf_int_out, sscanf_string_out);
    sscanf_ret_out = local_ret;
    dummy_output = dummy_input;
  end
endmodule
module RandomNumbers(
  input  integer seed_in,
  input  integer range_a_in,
  input  integer range_b_in,
  input  bit     dummy_input,
  output integer random_out,
  output integer urandom_out,
  output integer urandom_range_out,
  output bit     dummy_output
);
  always_comb begin
    automatic integer temp_int;
    random_out = $random();
    temp_int   = $random(seed_in);
    urandom_out = $urandom();
    temp_int    = $urandom(seed_in);
    urandom_range_out = $urandom_range(range_b_in);
    temp_int          = $urandom_range(range_a_in, range_b_in);
    dummy_output = dummy_input;
  end
endmodule
module DistributionFuncs(
  input  int param1_in,
  input  int param2_in,
  input  int param3_in,
  input  bit dummy_input,
  output int dist_uniform_out,
  output int dist_normal_out,
  output int dist_exponential_out,
  output int dist_poisson_out,
  output int dist_chi_square_out,
  output int dist_t_out,
  output int dist_erlang_out,
  output bit dummy_output
);
  always_comb begin
    $dist_uniform(dist_uniform_out, param1_in, param2_in);
    $dist_normal(dist_normal_out, param1_in, param2_in);
    $dist_exponential(dist_exponential_out, param1_in);
    $dist_poisson(dist_poisson_out, param1_in);
    $dist_chi_square(dist_chi_square_out, param1_in);
    $dist_t(dist_t_out, param1_in);
    $dist_erlang(dist_erlang_out, param1_in, param2_in);
    dummy_output = dummy_input;
  end
endmodule
module AssertionFuncs(
  input  logic clk,
  input  bit signal_in,
  input  bit predicate_in,
  input  integer delay_in,
  input  bit dummy_input,
  output logic rose_out,
  output logic fell_out,
  output logic stable_out,
  output logic changed_out,
  output logic past_default_out,
  output logic past_delay_out,
  output logic past_predicate_out,
  output logic past_all_args_out,
  output bit dummy_output
);
  always_ff @(posedge clk) begin
    rose_out          <= $rose(signal_in);
    fell_out          <= $fell(signal_in);
    stable_out        <= $stable(signal_in);
    changed_out       <= $changed(signal_in);
    past_default_out  <= $past(signal_in);
    past_delay_out    <= $past(signal_in, 2);
    past_predicate_out<= $past(signal_in, , predicate_in);
    past_all_args_out <= $past(signal_in, 2, predicate_in);
  end
  always_comb begin
    dummy_output = dummy_input;
  end
endmodule
module AnalysisFuncs(
  input  logic net_in,
  input  integer getpattern_in,
  input  string plusarg_string_in,
  input  bit    dummy_input,
  output integer countdrivers_ret1_out,
  output integer countdrivers_ret2_out,
  output integer countdrivers_ret3_out,
  output integer countdrivers_ret4_out,
  output integer countdrivers_ret5_out,
  output integer countdrivers_ret6_out,
  output integer countdrivers_num_out,
  output integer countdrivers_type_out,
  output integer countdrivers_strength_out,
  output integer countdrivers_and_out,
  output integer countdrivers_or_out,
  output logic [31:0] getpattern_out,
  output integer test_plusargs_out,
  output bit    dummy_output
);
  wire net_wire = net_in;
  always_comb begin
    automatic integer num_drivers;
    automatic integer type_out;
    automatic integer drive_strength;
    automatic integer and_conn;
    automatic integer or_conn;
    countdrivers_ret1_out = $countdrivers(net_wire);
    countdrivers_ret2_out = $countdrivers(net_wire, num_drivers);
    countdrivers_num_out  = num_drivers;
    countdrivers_ret3_out = $countdrivers(net_wire, num_drivers, type_out);
    countdrivers_type_out = type_out;
    countdrivers_ret4_out = $countdrivers(net_wire, num_drivers, type_out, drive_strength);
    countdrivers_strength_out = drive_strength;
    countdrivers_ret5_out = $countdrivers(net_wire, num_drivers, type_out, drive_strength, and_conn);
    countdrivers_and_out = and_conn;
    countdrivers_ret6_out = $countdrivers(net_wire, num_drivers, type_out, drive_strength, and_conn, or_conn);
    countdrivers_or_out = or_conn;
    getpattern_out = $getpattern(getpattern_in);
    test_plusargs_out = $test$plusargs(plusarg_string_in);
    dummy_output = dummy_input;
  end
endmodule
module EventTriggeredFunc(
  input  bit trigger_in,
  input  logic clk,
  input  bit dummy_input,
  output logic triggered_out,
  output bit dummy_output
);
  event my_event;
  always_ff @(posedge clk) begin
    if (trigger_in) -> my_event;
  end
  always @(my_event) begin
    triggered_out = my_event.triggered;
  end
  always_comb begin
    dummy_output = dummy_input;
  end
endmodule
module MiscSystemFuncs(
  input  bit dummy_input,
  output integer time_out,
  output integer stime_out,
  output real    realtime_out,
  output integer reset_count_out,
  output integer reset_value_out,
  output string  stacktrace_out,
  output bit     dummy_output
);
  always_comb begin
    time_out        = $time();
    stime_out       = $stime();
    realtime_out    = $realtime();
    reset_count_out = $reset_count();
    reset_value_out = $reset_value();
    stacktrace_out  = $stacktrace();
    dummy_output    = dummy_input;
  end
endmodule
module ScaleFunc(
  input  bit dummy_input,
  output integer scale_out,
  output bit dummy_output
);
  always_comb begin
    scale_out    = $scale(FileOps);
    dummy_output = dummy_input;
  end
endmodule
