interface simple_if_init_test;
  logic clk = 0;
  logic reset = 1;
endinterface
interface simple_if_access_test;
  logic if_member = 1;
endinterface
module operator_tests (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [127:0] wide_a,
    input logic [127:0] wide_b,
    input int shift_val_arith,
    input int shift_val_logic,
    input bit condition,
    output logic [7:0] sum,
    output logic [7:0] diff,
    output logic [7:0] mul,
    output logic [7:0] div,
    output logic [7:0] mod,
    output logic [7:0] band,
    output logic [7:0] bor,
    output logic [7:0] bxor,
    output logic [7:0] bnot_a,
    output logic [7:0] lshift,
    output logic [7:0] rshift,
    output logic [7:0] arith_lshift,
    output logic [7:0] arith_rshift,
    output logic reduction_and_a,
    output logic reduction_or_a,
    output logic reduction_xor_a,
    output logic land,
    output logic lor,
    output logic lnot_a,
    output logic lt,
    output logic le,
    output logic gt,
    output logic ge,
    output logic eq,
    output logic ne,
    output logic case_eq,
    output logic case_ne,
    output logic [7:0] mux_out,
    output logic [127:0] wide_sum,
    output logic [127:0] wide_band,
    output logic [7:0] power_res,
    output int dummy_op_out
);
    assign sum = a + b;
    assign diff = a - b;
    assign mul = a * b;
    assign div = a / b;
    assign mod = a % b;
    assign band = a & b;
    assign bor = a | b;
    assign bxor = a ^ b;
    assign bnot_a = ~a;
    assign lshift = a << shift_val_logic;
    assign rshift = a >> shift_val_logic;
    assign arith_lshift = a <<< shift_val_arith;
    assign arith_rshift = a >>> shift_val_arith;
    assign reduction_and_a = &a;
    assign reduction_or_a = |a;
    assign reduction_xor_a = ^a;
    assign land = (a > 0) && (b > 0);
    assign lor = (a == 0) || (b == 0);
    assign lnot_a = !(a == 0);
    assign lt = a < b;
    assign le = a <= b;
    assign gt = a > b;
    assign ge = a >= b;
    assign eq = a == b;
    assign ne = a != b;
    assign case_eq = (a === b);
    assign case_ne = (a !== b);
    assign mux_out = condition ? a : b;
    assign wide_sum = wide_a + wide_b;
    assign wide_band = wide_a & wide_b;
    assign power_res = a ** (b[1:0] + 1);
    assign dummy_op_out = sum[0] + diff[0] + mul[0] + div[0] + mod[0] + band[0] + bor[0] + bxor[0] + bnot_a[0] +
                          lshift[0] + rshift[0] + arith_lshift[0] + arith_rshift[0] + reduction_and_a +
                          reduction_or_a + reduction_xor_a + land + lor + lnot_a + lt + le + gt + ge + eq +
                          ne + case_eq + case_ne + mux_out[0] + wide_sum[0] + wide_band[0] + power_res[0] +
                          {a[1], b[1]}[0] + {4{a[2]}}[0];
endmodule
module constant_tests (
    input int trigger,
    output logic [15:0] param_logic_out,
    output logic [100:0] param_wide_100_out,
    output logic [200:0] param_wide_200_out,
    output real param_real_out,
    output longint param_quad_out,
    output string param_string_out,
    output logic [7:0] procedural_logic_out,
    output logic [100:0] procedural_wide_out,
    output real procedural_real_out,
    output longint procedural_quad_out,
    output string procedural_string_out,
    output logic [7:0] procedural_x_out,
    output real procedural_inf_out,
    output real procedural_nan_out,
    output int dummy_const_out
);
    parameter logic [15:0] P_LOGIC = 16'hABCD;
    parameter logic [100:0] P_WIDE_100 = 101'h1234567890ABCD_FEEDFACE_DEADBEEF;
    parameter logic [200:0] P_WIDE_200 = {80'h0, 121'h112233445566778899AA_BBCCDDEEFF001122334455_66778899AABBCCDDEEFF};
    parameter real P_REAL = 3.14159265;
    parameter longint P_QUAD = 64'h1234567890ABCDEF;
    parameter string P_STRING = "Constant String";
    assign param_logic_out = P_LOGIC;
    assign param_wide_100_out = P_WIDE_100;
    assign param_wide_200_out = P_WIDE_200;
    assign param_real_out = P_REAL;
    assign param_quad_out = P_QUAD;
    assign param_string_out = P_STRING;
    always_comb begin
        procedural_logic_out = 8'hEF;
        procedural_wide_out = 101'hFEDCBA9876543210_987654321_13579BDF02468ACE;
        procedural_real_out = 2.718;
        procedural_quad_out = 64'hFDEC_AB09_8765_4321;
        procedural_string_out = "Procedural String";
        procedural_x_out = 8'b1111_XXXX;
        procedural_inf_out = 1.0/0.0;
        procedural_nan_out = 0.0/0.0;
        dummy_const_out = trigger + param_logic_out[0] + param_wide_100_out[0] + param_wide_200_out[0] +
                          $itor(param_real_out) + $itor(param_quad_out) + param_string_out.len() +
                          procedural_logic_out[0] + procedural_wide_out[0] + $itor(procedural_real_out) +
                          $itor(procedural_quad_out) + procedural_string_out.len() + procedural_x_out[0] +
                          ($isinf(procedural_inf_out) ? 1 : 0) + ($isnan(procedural_nan_out) ? 1 : 0);
    end
endmodule
module display_scan_tests (
    input int val_int_d,
    input logic [15:0] val_logic_h,
    input bit [15:0] val_byte_c,
    input string val_string_s,
    input real val_real_efg,
    input time val_time_t_caret,
    input logic [31:0] packed_data_at,
    input int signed_val_tilde,
    input int unpacked_val_vuzp,
    input int fmt_width,
    input string scan_input_str,
    output int dummy_out_disp,
    output int scan_val_d,
    output logic [7:0] scan_val_h,
    output int file_scan_val_d,
    output real file_scan_val_f,
    output logic [63:0] sformat_out,
    output string sformatf_out,
    output int file_write_status,
    output int file_read_status
);
    integer file_handle_w;
    integer file_handle_r;
    string dummy_file_path = "vlt_temp_scan_test.txt";
    always_comb begin
        $display("Format tests:");
        $display("  %%d (int): %d", val_int_d);
        $display("  %%h (logic hex): %h", val_logic_h);
        $display("  %%x (logic hex): %x", val_logic_h);
        $display("  %%b (logic bin): %b", val_logic_h);
        $display("  %%o (logic octal): %o", val_logic_h);
        $display("  %%c (byte char, wider val): %c", val_byte_c);
        $display("  %%s (string): %s", val_string_s);
        $display("  %%s (packed as string): %s", packed_data_at);
        $display("  %%t (time): %t", val_time_t_caret);
        $display("  %%m (hier path): %m");
        $display("  %%v (unpacked V): %v", unpacked_val_vuzp);
        $display("  %%u (unpacked U): %u", unpacked_val_vuzp);
        $display("  %%z (unpacked Z): %z", unpacked_val_vuzp);
        $display("  %%e (real sci): %e", val_real_efg);
        $display("  %%f (real fix): %f", val_real_efg);
        $display("  %%g (real auto): %g", val_real_efg);
        $display("  %%p (pointer/object): %p", unpacked_val_vuzp);
        $display("  %%l (line): %l");
        $display("  %%~ (signed int): %~", signed_val_tilde);
        $display("  %%^ (realtime): %^", val_time_t_caret);
        $display("  %%@ (packed data): %@ ", packed_data_at);
        $display("  %%Nd (width): %10d", val_int_d);
        $display("  %%.*h (dynamic width): %.*h", fmt_width, val_logic_h);
        $write("Write Test: %d %h\n", val_int_d, val_logic_h);
        $sformat(sformat_out, "Sformat Test: int=%d hex=%h", val_int_d, val_logic_h);
        sformatf_out = $sformatf("Sformatf Test: real=%f", val_real_efg);
        file_handle_w = $fopen(dummy_file_path, "w");
        if (file_handle_w) begin
            file_write_status = $fwrite(file_handle_w, "d%d h%h f%f\n", val_int_d, val_logic_h, val_real_efg);
            $fclose(file_handle_w);
        end else begin
            file_write_status = -1;
        end
        file_handle_r = $fopen(dummy_file_path, "r");
        if (file_handle_r) begin
            int scan_d;
            logic [7:0] scan_h;
            real scan_f;
            file_read_status = $fscanf(file_handle_r, "d%d h%h f%f", scan_d, scan_h, scan_f);
            file_scan_val_d = scan_d;
            file_scan_val_f = scan_f;
            $fclose(file_handle_r);
        end else begin
            file_read_status = -1;
            file_scan_val_d = 0;
            file_scan_val_f = 0.0;
        end
        $sscanf(scan_input_str, "d%d h%h", scan_val_d, scan_val_h);
        dummy_out_disp = val_int_d + val_logic_h[0] + file_scan_val_d + $itor(file_scan_val_f) + scan_val_d + scan_val_h[0] +
                         sformat_out[0] + sformatf_out.len() + file_write_status + file_read_status;
    end
endmodule
module variable_types_init (
    input int init_trigger,
    output int dummy_out_v,
    output int simple_int_val,
    output logic wide_logic_val_0,
    output int packed_s_field1_0,
    output int unpacked_s_int_val,
    output int unpacked_s_str_len,
    output int packed_u_int_val,
    output int unpacked_u_int_val,
    output int unpacked_array_val_0,
    output int assoc_array_str_len,
    output int assoc_array_int_val_5,
    output int wildcard_array_int_val,
    output int dyn_array_val_0_bit0,
    output int queue_val_0_itor,
    output int sample_queue_size,
    output int forkjoin_handle_val,
    output int delay_sched_val,
    output int trigger_sched_val,
    output int dynamic_trigger_sched_val,
    output int random_gen_val,
    output logic iface_clk_val,
    output int local_var_val,
    output logic local_wide_val_0,
    output int class_member_val,
    output int class_local_member_val,
    output logic class_wide_member_val_0,
    output int proc_var_init_val,
    output int event_var_val,
    output int sem_var_wait_status,
    output int mutex_var_lock_status,
    output int mb_var_count,
    output int rand_state_val_itor,
    output int file_desc_val,
    output logic x_init_bit_val,
    output int _underline_var_val,
    output logic simple_logic_no_init_val,
    output int unpacked_struct_dyn_array_memA_out
);
    int simple_int_no_init;
    real simple_real_init = 3.14;
    string simple_string_init = "hello";
    logic [15:0] logic_vec_init = 16'hABCD;
    logic [100:0] wide_logic_no_init;
    bit [7:0] bit_vec_init = 8'b10101010;
    integer file_desc_var = 0;
    integer file_desc_no_init;
    logic [7:0] x_init_var = 8'hX;
    logic simple_logic_no_init;
    struct packed {
        logic [15:0] field1_p;
        logic [15:0] field2_p;
    } packed_s_no_init;
    struct unpacked {
        int u_int;
        string u_str;
        real u_real;
    } unpacked_s_no_init;
    union packed {
        logic [31:0] u_p_vec;
        int u_p_int;
        real u_p_real;
    } packed_u_no_init;
    union unpacked {
        int u_u_int;
        real u_u_real;
    } unpacked_u_no_init;
    enum {STATE_A, STATE_B, STATE_C} enum_var_no_init = STATE_A;
    int unpacked_array_no_init[4];
    logic unpacked_array_init[2] = '{0, 1};
    int assoc_array_int_init[int] = '{5: 100, 10: 200, default: -1};
    string assoc_array_str_no_init[string];
    int wildcard_array_int_init[*] = '{5: 100, default: -1};
    int dyn_array_no_init[];
    real dyn_array_init[] = {1.0, 2.0, 3.0};
    int queue_int_no_init[$];
    real queue_real_init[$] = {4.0, 5.0};
    string sample_queue_no_init [:] = new(2);
    process proc_var_no_init = null;
    event event_var_no_init;
    semaphore sem_var_no_init = new(1);
    mutex mutex_var_no_init = new;
    mailbox mb_var_no_init = new(4);
    randstate rand_state_var_no_init;
    forkjoin_handle forkjoin_handle_no_init;
    delay_scheduler delay_scheduler_no_init;
    trigger_scheduler trigger_scheduler_no_init;
    dynamic_trigger_scheduler dynamic_trigger_scheduler_no_init;
    random_generator random_gen_no_init;
    class MyClassInitTest;
        int member = 123;
        logic [63:0] wide_member = 64'hFEED_FACE_DEAD_BEEF;
        local int local_member = 456;
        function new();
          local_member = 0;
        endfunction
        function automatic int get_local_member(); return local_member; endfunction
    endclass
    MyClassInitTest class_ref_no_init = null;
    MyClassInitTest class_ref_procedural_init = null;
    simple_if_init_test iface_inst_no_init();
    int _underline_var_no_init;
    string dummy_file_path = "/dev/null";
    struct unpacked {
        int memberA;
        real memberB;
    } unpacked_struct_def;
    unpacked_struct_def unpacked_struct_dyn_array[];
    always_comb begin
        int local_var_no_init;
        string local_string_init = $sformatf("local %0d", init_trigger);
        logic [63:0] local_wide_no_init;
        int _local_underline_var;
        integer local_file_desc_no_init;
        wide_logic_no_init = 101'hFEDCBA9876543210_987654321_13579BDF02468ACE;
        simple_int_no_init = init_trigger;
        packed_s_no_init.field1_p = init_trigger[15:0];
        packed_s_no_init.field2_p = init_trigger[15:0] + 1;
        unpacked_s_no_init.u_int = init_trigger + 2;
        unpacked_s_no_init.u_str = $sformatf("unpacked %0d", init_trigger);
        unpacked_s_no_init.u_real = $itor(init_trigger) + 2.0;
        packed_u_no_init.u_p_int = init_trigger + 3;
        packed_u_no_init.u_p_vec = packed_u_no_init.u_p_int;
        packed_u_no_init.u_p_real = $itor(init_trigger) + 3.0;
        unpacked_u_no_init.u_u_int = init_trigger + 4;
        unpacked_u_no_init.u_u_real = $itor(init_trigger) + 4.0;
        if (init_trigger >= 0 && init_trigger < 4) unpacked_array_no_init[init_trigger] = init_trigger + 5;
        else unpacked_array_no_init[0] = 0;
        assoc_array_str_no_init["key"] = $sformatf("assoc str %0d", init_trigger);
        if (init_trigger >= 0 && init_trigger < 100) wildcard_array_int_init[init_trigger] = init_trigger + 10;
        iface_inst_no_init.clk = init_trigger[0];
        local_var_no_init = init_trigger * 10;
        local_wide_no_init = init_trigger * 100;
        _underline_var_no_init = init_trigger + 7;
        _local_underline_var = init_trigger + 8;
        file_desc_no_init = $fopen(dummy_file_path, "w");
        if (file_desc_no_init > 0) $fclose(file_desc_no_init);
        local_file_desc_no_init = $fopen(dummy_file_path, "w");
        if (local_file_desc_no_init > 0) $fclose(local_file_desc_no_init);
        if (class_ref_procedural_init == null) begin
            class_ref_procedural_init = new();
        end
        class_member_val = (class_ref_procedural_init != null) ? class_ref_procedural_init.member : 0;
        class_local_member_val = (class_ref_procedural_init != null) ? class_ref_procedural_init.get_local_member() : 0;
        class_wide_member_val_0 = (class_ref_procedural_init != null) ? class_ref_procedural_init.wide_member[0] : 0;
        if (dyn_array_no_init.size() != 5) begin
            dyn_array_no_init = new[5];
        end
        if (dyn_array_no_init.size() > 0) begin
             dyn_array_no_init[0] = init_trigger[7:0];
        end
        if (queue_int_no_init.size() != 3) queue_int_no_init = {1,2,3};
        if (queue_int_no_init.size() > 0) begin void'(queue_int_no_init.push_back(init_trigger)); void'(queue_int_no_init.pop_front()); end
        if (sample_queue_no_init.size() != 2) begin sample_queue_no_init = new(2); sample_queue_no_init[0] = "a"; sample_queue_no_init[1] = "b"; end
        sample_queue_size = sample_queue_no_init.size();
        if (unpacked_struct_dyn_array.size() != 2) begin
            unpacked_struct_dyn_array = new[2];
            for (int i = 0; i < unpacked_struct_dyn_array.size(); ++i) begin
                 unpacked_struct_dyn_array[i].memberA = -10;
                 unpacked_struct_dyn_array[i].memberB = -10.0;
            end
        end
        if (unpacked_struct_dyn_array.size() > 0) begin
            unpacked_struct_dyn_array[0].memberA = init_trigger + 100;
            unpacked_struct_dyn_array[0].memberB = $itor(init_trigger) + 100.0;
        end
        unpacked_struct_dyn_array_memA_out = (unpacked_struct_dyn_array.size() > 0) ? unpacked_struct_dyn_array[0].memberA : 0;
        forkjoin_handle_val = (forkjoin_handle_no_init == 0) ? 0 : 1;
        delay_sched_val = (delay_scheduler_no_init == 0) ? 0 : 1;
        trigger_sched_val = (trigger_scheduler_no_init == 0) ? 0 : 1;
        dynamic_trigger_sched_val = (dynamic_trigger_scheduler_no_init == 0) ? 0 : 1;
        random_gen_val = (random_gen_no_init == 0) ? 0 : 1;
        simple_int_val = simple_int_no_init;
        wide_logic_val_0 = wide_logic_no_init[0];
        packed_s_field1_0 = packed_s_no_init.field1_p[0];
        unpacked_s_int_val = unpacked_s_no_init.u_int;
        unpacked_s_str_len = unpacked_s_no_init.u_str.len();
        packed_u_no_init.u_p_int = init_trigger + 3;
        packed_u_int_val = packed_u_no_init.u_p_int;
        unpacked_u_int_val = unpacked_u_no_init.u_u_int;
        unpacked_array_val_0 = unpacked_array_no_init[0];
        assoc_array_str_len = assoc_array_str_no_init.exists("key") ? assoc_array_str_no_init["key"].len() : 0;
        assoc_array_int_val_5 = assoc_array_int_init.exists(5) ? assoc_array_int_init[5] : assoc_array_int_init.atDefault();
        wildcard_array_int_val = wildcard_array_int_init.exists(init_trigger) ? wildcard_array_int_init[init_trigger] : wildcard_array_int_init.atDefault();
        dyn_array_val_0_bit0 = dyn_array_no_init.size() > 0 ? int'(dyn_array_no_init[0][0]) : 0;
        queue_val_0_itor = queue_real_init.size() > 0 ? $itor(queue_real_init[0]) : 0;
        iface_clk_val = iface_inst_no_init.clk;
        local_var_val = local_var_no_init;
        local_wide_val_0 = local_wide_no_init[0];
        _underline_var_val = _underline_var_no_init;
        file_desc_val = file_desc_no_init;
        x_init_bit_val = x_init_var[0];
        simple_logic_no_init_val = simple_logic_no_init;
        proc_var_init_val = (proc_var_no_init == null) ? 0 : 1;
        event_var_val = 0;
        sem_var_wait_status = sem_var_no_init.try_wait();
        mutex_var_lock_status = mutex_var_no_init.try_lock();
        int count = 0;
        void'(mb_var_no_init.try_get(count));
        void'(mb_var_no_init.put(count));
        mb_var_count = mb_var_no_init.num();
        rand_state_val_itor = (rand_state_var_no_init == 0) ? 0 : 1;
    end
    assign dummy_out_v = simple_int_val + wide_logic_val_0 + packed_s_field1_0 + unpacked_s_int_val +
                       unpacked_s_str_len + packed_u_int_val + unpacked_u_int_val +
                       unpacked_array_val_0 + assoc_array_str_len + assoc_array_int_val_5 + wildcard_array_int_val +
                       dyn_array_val_0_bit0 + queue_val_0_itor + sample_queue_size + forkjoin_handle_val + delay_sched_val + trigger_sched_val + dynamic_trigger_sched_val + random_gen_val + (iface_clk_val ? 1 : 0) + local_var_val + (local_wide_val_0 ? 1 : 0) +
                       class_member_val + class_local_member_val + (class_wide_member_val_0 ? 1 : 0) + proc_var_init_val + event_var_val + sem_var_wait_status +
                       mutex_var_lock_status + mb_var_count + rand_state_val_itor + file_desc_val +
                       (x_init_bit_val ? 1 : 0) + _underline_var_val + (simple_logic_no_init_val ? 1 : 0) + unpacked_struct_dyn_array_memA_out;
endmodule
module access_dereference_tests (
    input int access_in,
    input int array_idx,
    input string assoc_key,
    output int class_public_member_out,
    output int class_local_method_out,
    output int struct_member_out,
    output int union_member_out,
    output int unpacked_array_element_out,
    output int assoc_array_element_out,
    output logic iface_member_out,
    output int dummy_access_out
);
    class MyClassAccess;
        int public_member = 1;
        local int local_member = 2;
        function new();
          public_member = 10;
          local_member = 20;
        endfunction
        function automatic int get_local();
          return local_member;
        endfunction
    endclass
    struct unpacked {
        int member1;
        real member2;
    } unpacked_s;
    union unpacked {
        int u_member1;
        real u_member2;
    } unpacked_u;
    int unpacked_array[10];
    int assoc_array[string];
    MyClassAccess inst_var = null;
    simple_if_access_test iface_inst();
    always_comb begin
        if (inst_var == null) begin
            inst_var = new();
        end
        if (inst_var != null) begin
            inst_var.public_member = access_in;
            class_public_member_out = inst_var.public_member;
            class_local_method_out = inst_var.get_local();
        end else begin
            class_public_member_out = 0;
            class_local_method_out = 0;
        end
        unpacked_s.member1 = access_in + 10;
        unpacked_s.member2 = $itor(access_in) + 10.5;
        struct_member_out = unpacked_s.member1;
        unpacked_u.u_member1 = access_in + 20;
        unpacked_u.u_member2 = $itor(access_in) + 20.5;
        union_member_out = unpacked_u.u_member1;
        if (array_idx >= 0 && array_idx < 10) begin
            unpacked_array[array_idx] = access_in + 30;
            unpacked_array_element_out = unpacked_array[array_idx];
        end else begin
            unpacked_array_element_out = 0;
        end
        assoc_array[assoc_key] = access_in + 40;
        assoc_array_element_out = assoc_array.exists(assoc_key) ? assoc_array[assoc_key] : 0;
        iface_member_out = iface_inst.if_member;
        dummy_access_out = class_public_member_out + class_local_method_out + struct_member_out + union_member_out + unpacked_array_element_out + assoc_array_element_out + (iface_member_out ? 1 : 0);
    end
endmodule
module type_conversion_tests (
    input logic [127:0] wide_scalar_in,
    input logic [31:0] packed_in,
    input real real_in,
    input int int_in,
    input logic [15:0] logic_vec_in,
    input string string_in,
    output logic [31:0] unpacked_array_out [4],
    output string packed_to_string_out,
    output int real_to_int_out,
    output real int_to_real_out,
    output logic [15:0] int_to_logic_out,
    output int logic_to_int_out,
    output int dummy_out_tc,
    output logic [31:0] implicit_wide_to_packed_out,
    output logic [127:0] implicit_packed_to_wide_out,
    output int string_to_int_out
);
    struct packed {
        logic [15:0] field1_p;
        logic [15:0] field2_p;
    } packed_struct_var_src, packed_struct_var_dest;
    struct unpacked {
        int fieldA_u;
        real fieldB_u;
    } unpacked_struct_var_src, unpacked_struct_var_dest;
    logic [31:0] wide_to_packed_var;
    logic [127:0] packed_to_wide_var;
    always_comb begin
        wide_to_packed_var = wide_scalar_in;
        packed_to_wide_var = packed_in;
        unpacked_array_out = wide_scalar_in;
        packed_to_string_out = $sformatf("Packed value as string: %s", packed_in);
        real_to_int_out = int'(real_in);
        int_to_real_out = real'(int_in);
        int_to_logic_out = 16'(int_in);
        logic_to_int_out = int'(logic_vec_in);
        string_to_int_out = int'(string_in);
        packed_struct_var_src.field1_p = int_in[15:0] + 1;
        packed_struct_var_src.field2_p = packed_in[15:0];
        packed_struct_var_dest = packed_struct_var_src;
        unpacked_struct_var_src.fieldA_u = int_in + 2;
        unpacked_struct_var_src.fieldB_u = real_in + 1.0;
        unpacked_struct_var_dest = unpacked_struct_var_src;
        implicit_wide_to_packed_out = wide_to_packed_var;
        implicit_packed_to_wide_out = packed_to_wide_var;
        dummy_out_tc = unpacked_array_out[0][0] + real_to_int_out + logic_to_int_out +
                       packed_struct_var_dest.field1_p[0] + $itor(unpacked_struct_var_dest.fieldB_u) +
                       string_to_int_out + implicit_wide_to_packed_out[0] + implicit_packed_to_wide_out[0] +
                       packed_to_string_out.len() + int_to_logic_out[0];
    end
endmodule
module dpi_tests (
    input int dpi_in1,
    input byte dpi_in2,
    input logic [31:0] dpi_wide_in,
    input int dpi_arg3,
    output int dpi_out_int,
    output logic [31:0] dpi_out_wide,
    output int dummy_out_dpi
);
    import "DPI-C" function int my_dpi_func(input int a, input byte b, input int c);
    import "DPI-C" task my_dpi_task(input logic [31:0] data);
    int dpi_result_int = 0;
    logic [31:0] task_data_echo = 0;
    always_comb begin
        dpi_result_int = my_dpi_func(dpi_in1, dpi_in2, dpi_arg3);
        my_dpi_task(dpi_wide_in);
        task_data_echo = dpi_wide_in;
        dummy_out_dpi = dpi_result_int + task_data_echo[0];
    end
    assign dpi_out_int = dpi_result_int;
    assign dpi_out_wide = task_data_echo;
endmodule
module select_concat_tests (
    input logic [63:0] data_in,
    input int index_in,
    input int width_in,
    input int array_index_in,
    output logic [15:0] part_select_out,
    output logic [31:0] dynamic_part_select_out,
    output logic [31:0] concatenation_out,
    output logic [7:0] replication_concat_out,
    output logic [7:0] dynamic_array_element_out,
    output logic [7:0] fixed_array_element_out,
    output int dummy_selcon_out
);
    logic [7:0] dynamic_array [];
    logic [7:0] fixed_array [5];
    always_comb begin
        part_select_out = data_in[63:48];
        concatenation_out = {data_in[31:0], data_in[63:32]};
        replication_concat_out = {8{data_in[0]}};
        dynamic_part_select_out = 32'bX;
        if (index_in >= 0 && width_in > 0 && (index_in + width_in) <= 64) begin
             dynamic_part_select_out = data_in[index_in +: width_in];
        end else begin
             dynamic_part_select_out = 32'b0;
        end
        if (dynamic_array.size() != 10) begin
            dynamic_array = new[10];
        end
        dynamic_array_element_out = 8'bX;
        if (array_index_in >= 0 && array_index_in < dynamic_array.size()) begin
             dynamic_array[array_index_in] = data_in[7:0];
             dynamic_array_element_out = dynamic_array[array_index_in];
        end else if (dynamic_array.size() > 0) begin
            dynamic_array_element_out = dynamic_array[0];
        end else begin
             dynamic_array_element_out = 8'b0;
        end
        fixed_array_element_out = 8'bX;
        if (array_index_in >= 0 && array_index_in < 5) begin
            fixed_array[array_index_in] = data_in[15:8];
            fixed_array_element_out = fixed_array[array_index_in];
        end else begin
            fixed_array_element_out = fixed_array[0];
        end
        dummy_selcon_out = part_select_out[0] + dynamic_part_select_out[0] + concatenation_out[0] + replication_concat_out[0] + dynamic_array_element_out[0] + fixed_array_element_out[0];
    end
endmodule
module function_call_tests (
    input int input_val,
    input logic [7:0] array_in[2],
    output int func_out,
    output int task_array_sum_out,
    output int class_method_out,
    output int dummy_func_out
);
    function automatic int my_local_func(input int arg);
        return arg * 2;
    endfunction
    task automatic my_local_task_with_array(input logic [7:0] arr[2], output int sum);
        sum = arr[0] + arr[1];
    endtask
    class MyMethodClass;
        int member = 100;
        function automatic int get_member_value(input int offset);
            return member + offset;
        endfunction
    endclass
    MyMethodClass method_inst = null;
    always_comb begin
        int task_sum = 0;
        if (method_inst == null) begin
            method_inst = new();
        end
        func_out = my_local_func(input_val);
        my_local_task_with_array(array_in, task_sum);
        task_array_sum_out = task_sum;
        if (method_inst != null) begin
            class_method_out = method_inst.get_member_value(input_val);
        end else begin
            class_method_out = 0;
        end
        dummy_func_out = func_out + task_array_sum_out + class_method_out;
    end
endmodule
module streaming_operators_test (
    input logic [63:0] data_in,
    input int start_byte,
    output logic [31:0] stream_out [2],
    output logic [63:0] stream_concat_out,
    output int dummy_stream_out
);
    logic [7:0] byte_stream [];
    always_comb begin
        stream_out = {>>32{data_in}};
        stream_concat_out = {>>8{data_in}};
        if (byte_stream.size() != 8) begin
             byte_stream = new[8];
        end
        byte_stream = {<<8{data_in}};
        dummy_stream_out = stream_out[0][0] + stream_concat_out[0] + (byte_stream.size() > 0 ? byte_stream[0] : 0) + start_byte;
    end
endmodule
module struct_union_packed_unpacked_test (
    input logic [31:0] packed_data,
    input int unpacked_int_data,
    output logic [31:0] packed_struct_out,
    output int unpacked_struct_int_out,
    output logic [31:0] packed_union_out,
    output real unpacked_union_real_out,
    output int dummy_struct_union_out
);
    struct packed {
        logic [15:0] field1_p;
        logic [15:0] field2_p;
    } packed_s_var;
    struct unpacked {
        int fieldA_u;
        real fieldB_u;
    } unpacked_s_var;
    union packed {
        logic [31:0] u_p_vec;
        int u_p_int;
        real u_p_real;
    } packed_u_var;
    union unpacked {
        int u_u_int;
        real u_u_real;
    } unpacked_u_var;
    always_comb begin
        packed_s_var.field1_p = packed_data[15:0];
        packed_s_var.field2_p = packed_data[31:16];
        packed_struct_out = packed_s_var;
        unpacked_s_var.fieldA_u = unpacked_int_data;
        unpacked_s_var.fieldB_u = $itor(unpacked_int_data) + 0.5;
        unpacked_struct_int_out = unpacked_s_var.fieldA_u;
        packed_u_var.u_p_vec = packed_data;
        packed_union_out = packed_u_var.u_p_vec;
        unpacked_u_var.u_u_int = unpacked_int_data + 10;
        unpacked_u_var.u_u_real = $itor(unpacked_int_data) + 1.5;
        unpacked_union_real_out = unpacked_u_var.u_u_real;
        dummy_struct_union_out = packed_struct_out[0] + unpacked_struct_int_out + packed_union_out[0] + $itor(unpacked_union_real_out);
    end
endmodule
module constant_wide_access_test (
    input int index,
    output logic [31:0] const_wide_word_out,
    output int dummy_const_wide_out
);
    parameter logic [127:0] P_WIDE_CONST = 128'h11223344_55667788_99AABBCC_DDEEFF00;
    logic [127:0] local_wide_var;
    always_comb begin
        local_wide_var = P_WIDE_CONST;
        const_wide_word_out = 32'bX;
        if (index >= 0 && index < 4) begin
            const_wide_word_out = local_wide_var[index * 32 +: 32];
        end else begin
             const_wide_word_out = 32'b0;
        end
        dummy_const_wide_out = const_wide_word_out[0];
    end
endmodule
