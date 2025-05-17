class SvReportEntry;
    static int s_entry_count = 0;
    string m_key;
    real m_value;
    function new(string key, real value);
        m_key = key;
        m_value = value;
        s_entry_count++;
    endfunction
    function string getKey();
        return m_key;
    endfunction
    function real getValue();
        return m_value;
    endfunction
    static function int getEntryCount();
        return s_entry_count;
    endfunction
endclass
interface data_bus_if #(parameter DATA_WIDTH = 32);
    logic clk;
    logic reset;
    logic [DATA_WIDTH-1:0] addr;
    logic [DATA_WIDTH-1:0] data;
    logic write_en;
    logic read_en;
    logic busy;
    modport master (output clk, output reset, output addr, output data, output write_en, output read_en, input busy);
    modport slave (input clk, input reset, input addr, input data, input write_en, input read_en, output busy);
endinterface
module ArithOpsInts (
    input int i_a,
    input int i_b,
    output int o_add,
    output int o_sub,
    output longint o_mul,
    output int o_div,
    output int o_mod
);
    longint mul_res;
    always_comb begin
        mul_res = $cast(longint, i_a) * $cast(longint, i_b);
    end
    assign o_add = i_a + i_b;
    assign o_sub = i_a - i_b;
    assign o_mul = mul_res;
    assign o_div = (i_b != 0) ? i_a / i_b : 0;
    assign o_mod = (i_b != 0) ? i_a % i_b : 0;
endmodule
module LogicBitwiseReduct (
    input bit [7:0] i_vec_in,
    input logic [3:0] i_logic_vec_in,
    output bit o_and_v,
    output bit o_or_v,
    output bit o_xor_v,
    output logic o_and_l,
    output logic o_or_l,
    output logic o_xor_l
);
    assign o_and_v = &i_vec_in;
    assign o_or_v = |i_vec_in;
    assign o_xor_v = ^i_vec_in;
    assign o_and_l = &i_logic_vec_in;
    assign o_or_l = |i_logic_vec_in;
    assign o_xor_l = ^i_logic_vec_in;
endmodule
module SeqRegFile (
    input bit clk,
    input bit reset,
    input bit [7:0] i_write_data,
    input bit [2:0] i_write_addr,
    input bit [2:0] i_read_addr,
    input bit i_write_en,
    output bit [7:0] o_read_data
);
    logic [7:0] register_file [0:7];
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            register_file <= '{default: '0};
        end else begin
            if (i_write_en) begin
                register_file[i_write_addr] <= i_write_data;
            end
        end
    end
    assign o_read_data = register_file[i_read_addr];
endmodule
module CombMux4to1 (
    input bit [1:0] i_select,
    input bit [7:0] i_data0,
    input bit [7:0] i_data1,
    input bit [7:0] i_data2,
    input bit [7:0] i_data3,
    output bit [7:0] o_mux_out
);
    logic [7:0] temp_out;
    always_comb begin
        case (i_select)
            2'b00: temp_out = i_data0;
            2'b01: temp_out = i_data1;
            2'b10: temp_out = i_data2;
            2'b11: temp_out = i_data3;
            default: temp_out = 'x;
        endcase
    end
    assign o_mux_out = temp_out;
endmodule
module CaseZCaseXDecoder (
    input bit [3:0] i_opcode,
    output bit [7:0] o_control_signal
);
    logic [7:0] control_reg;
    always_comb begin
        casex (i_opcode)
            4'b101z: control_reg = 8'hA1;
            4'b01z?: control_reg = 8'hB2;
            4'b1x0x: control_reg = 8'hC3;
            default: control_reg = '0;
        endcase
    end
    assign o_control_signal = control_reg;
endmodule
module ForLoopSum (
    input int i_limit,
    output int o_sum_up_to_limit
);
    int sum_reg;
    always_comb begin
        sum_reg = 0;
        for (int k=1; k <= i_limit; k++) begin
            sum_reg += k;
        end
    end
    assign o_sum_up_to_limit = sum_reg;
endmodule
module WhileLoopCounter (
    input int i_start,
    input int i_end,
    output int o_count
);
    int count_reg;
    int current;
    always_comb begin
        count_reg = 0;
        current = i_start;
        while (current < i_end) begin
            count_reg++;
            current += 1;
        end
    end
    assign o_count = count_reg;
endmodule
module TypedefStructUnionEnumPackedExample (
    input bit [2:0] i_command,
    input bit [31:0] i_payload_in,
    output bit [7:0] o_status_byte,
    output bit [15:0] o_address_field
);
    typedef enum logic [2:0] { CMD_READ, CMD_WRITE, CMD_STATUS, CMD_ERROR } Command_e;
    typedef struct packed {
        bit [7:0] status;
        bit [23:0] data;
    } StatusPacket_s;
    typedef union packed {
        bit [31:0] word;
        bit [15:0] half_word [2];
        bit [7:0] byte [4];
    } DataPayload_u;
    Command_e current_command;
    StatusPacket_s status_pkt;
    DataPayload_u payload_u;
    always_comb begin
        case (i_command)
            3'b000: current_command = CMD_READ;
            3'b001: current_command = CMD_WRITE;
            3'b010: current_command = CMD_STATUS;
            default: current_command = CMD_ERROR;
        endcase
        payload_u.word = i_payload_in;
        status_pkt.status = payload_u.byte[0];
        status_pkt.data = payload_u.word[23:0];
        o_status_byte = (current_command == CMD_STATUS) ? status_pkt.status : '0;
        o_address_field = payload_u.half_word[0];
    end
endmodule
module TypedefStructUnionEnumUnpackedExample (
    input int i_event_code,
    input bit [63:0] i_event_data,
    output bit o_is_critical,
    output string o_event_name,
    output longint o_data_value
);
    typedef enum { EVENT_INFO, EVENT_WARNING, EVENT_CRITICAL } EventLevel_e;
    typedef struct {
        EventLevel_e level;
        string name;
        longint value;
    } Event_s;
    typedef union {
        longint l_val;
        real r_val;
    } Data_unpacked_u;
    Event_s current_event;
    Data_unpacked_u data_u;
    always_comb begin
        case (i_event_code)
            0: begin current_event.level = EVENT_INFO; current_event.name = "Info"; end
            1: begin current_event.level = EVENT_WARNING; current_event.name = "Warning"; end
            default: begin current_event.level = EVENT_CRITICAL; current_event.name = "Critical"; end
        endcase
        current_event.value = $cast(longint, i_event_data);
        data_u.l_val = current_event.value;
        o_is_critical = (current_event.level == EVENT_CRITICAL);
        o_event_name = current_event.name;
        o_data_value = data_u.l_val;
    end
endmodule
module FixedDynamicArraysOps (
    input bit clk,
    input bit reset,
    input bit [7:0] i_fixed_data [0:3],
    input int i_dynamic_size,
    input bit [7:0] i_dynamic_init_val,
    output bit [7:0] o_fixed_sum,
    output int o_dynamic_size,
    output int o_dynamic_sum
);
    logic [7:0] fixed_arr [0:3];
    logic [7:0] dynamic_arr [];
    int dynamic_sum_reg = 0;
    int fixed_sum_reg = 0;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            fixed_arr <= '{default: '0};
            dynamic_arr <= new[0];
            dynamic_sum_reg <= 0;
            fixed_sum_reg <= 0;
        end else begin
            fixed_arr <= i_fixed_data;
            fixed_sum_reg <= fixed_arr.sum();
            if (i_dynamic_size >= 0 && i_dynamic_size <= 8) begin
                dynamic_arr <= new[i_dynamic_size];
                dynamic_sum_reg <= 0;
                for (int k=0; k < dynamic_arr.size(); k++) begin
                    dynamic_arr[k] <= i_dynamic_init_val + k;
                end
                foreach (dynamic_arr[idx]) begin
                    dynamic_sum_reg += dynamic_arr[idx];
                end
            end else begin
                dynamic_arr <= new[0];
                dynamic_sum_reg <= 0;
            end
        end
    end
    assign o_fixed_sum = $cast(bit[7:0])(fixed_sum_reg);
    assign o_dynamic_size = dynamic_arr.size();
    assign o_dynamic_sum = dynamic_sum_reg;
endmodule
module AssociativeQueueArraysOps (
    input bit clk,
    input bit reset,
    input int i_assoc_key_w,
    input int i_assoc_data_w,
    input int i_assoc_key_r,
    input int i_queue_push_val,
    input bit i_assoc_write_en,
    input bit i_assoc_delete_en,
    input bit i_queue_push_en,
    input bit i_queue_pop_en,
    output int o_assoc_read_val,
    output bit o_assoc_exists,
    output int o_queue_front,
    output int o_queue_size
);
    int assoc_arr [int];
    int data_queue [$];
    int assoc_read_reg = 0;
    bit assoc_exists_reg = 0;
    int queue_front_reg = 0;
    int queue_size_reg = 0;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            assoc_arr = assoc_arr.delete();
            data_queue = {};
        end else begin
            if (i_assoc_write_en) begin
                assoc_arr[i_assoc_key_w] <= i_assoc_data_w;
            end
            if (i_assoc_delete_en && assoc_arr.exists(i_assoc_key_w)) begin
                assoc_arr.delete(i_assoc_key_w);
            end
            if (i_queue_push_en) begin
                data_queue.push_back(i_queue_push_val);
            end else if (i_queue_pop_en && data_queue.size() > 0) begin
                void'(data_queue.pop_front());
            end
        end
    end
    always_comb begin
        assoc_exists_reg = assoc_arr.exists(i_assoc_key_r);
        assoc_read_reg = assoc_arr.exists(i_assoc_key_r) ? assoc_arr[i_assoc_key_r] : 0;
        queue_size_reg = data_queue.size();
        queue_front_reg = (data_queue.size() > 0) ? data_queue[0] : 0;
    end
    assign o_assoc_read_val = assoc_read_reg;
    assign o_assoc_exists = assoc_exists_reg;
    assign o_queue_front = queue_front_reg;
    assign o_queue_size = queue_size_reg;
endmodule
module ArrayMethodsProcessingSimple (
    input int i_data_in [0:3],
    input int i_find_val,
    output int o_sum,
    output int o_min,
    output int o_max,
    output int o_first_idx,
    output int o_unique_size
);
    int data_arr [0:3];
    int sum_res;
    int min_res;
    int max_res;
    int first_idx_res;
    int unique_size_res;
    always_comb begin
        data_arr = i_data_in;
        sum_res = data_arr.sum();
        min_res = data_arr.min();
        max_res = data_arr.max();
        first_idx_res = data_arr.first(item == i_find_val);
        unique_size_res = data_arr.unique().size();
    end
    assign o_sum = sum_res;
    assign o_min = min_res;
    assign o_max = max_res;
    assign o_first_idx = first_idx_res;
    assign o_unique_size = unique_size_res;
endmodule
module ClassProceduralInstantiationExample (
    input bit clk,
    input bit reset,
    input bit i_create_trigger,
    input bit i_destroy_trigger,
    input real i_value_in,
    output real o_item_value,
    output int o_total_items
);
    SvReportEntry current_entry = null;
    real item_value_reg = -1.0;
    int total_items_reg = 0;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            if (current_entry != null) begin
                current_entry = null;
            end
            item_value_reg <= -1.0;
            total_items_reg <= SvReportEntry::getEntryCount();
        end else begin
            if (i_create_trigger && current_entry == null) begin
                current_entry <= new("ReportData", i_value_in);
            end
            if (i_destroy_trigger && current_entry != null) begin
                 current_entry = null;
            end
            if (current_entry != null) begin
                 item_value_reg <= current_entry.getValue();
            end else begin
                 item_value_reg <= -1.0;
            end
            total_items_reg <= SvReportEntry::getEntryCount();
        end
    end
    assign o_item_value = item_value_reg;
    assign o_total_items = total_items_reg;
endmodule
module FunctionTaskCallExample (
    input bit clk,
    input bit reset,
    input int i_arg1,
    input int i_arg2,
    input bit i_use_task,
    output int o_result,
    output bit o_task_done
);
    int result_reg = 0;
    logic task_done_flag = 0;
    function automatic int func_multiply(int a, int b);
        return a * b;
    endfunction
    task automatic task_divide(input int a, input int b, output int res);
        if (b != 0) res = a / b;
        else res = 0;
    endtask
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            result_reg <= 0;
            task_done_flag <= 0;
        end else begin
            task_done_flag <= 0;
            if (i_use_task) begin
                task_divide(i_arg1, i_arg2, result_reg);
                task_done_flag <= 1;
            end else begin
                result_reg <= func_multiply(i_arg1, i_arg2);
                task_done_flag <= 1;
            end
        end
    end
    assign o_result = result_reg;
    assign o_task_done = task_done_flag;
endmodule
module ParametersLocalparamConstExample #(parameter P_OFFSET = 5) (
    input int i_data,
    output int o_shifted_masked_added
);
    localparam LP_SCALE = 2;
    const int CONST_THRESHOLD = 100;
    int temp_res;
    always_comb begin
        temp_res = (i_data * LP_SCALE) + P_OFFSET;
        if (temp_res > CONST_THRESHOLD) begin
            temp_res = CONST_THRESHOLD;
        end
    end
    assign o_shifted_masked_added = temp_res;
endmodule
module GenerateBlocksExample #(parameter WIDTH = 4) (
    input bit [WIDTH-1:0] i_data_a,
    input bit [WIDTH-1:0] i_data_b,
    input bit i_select_add,
    output bit [WIDTH-1:0] o_result
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : bit_op_gen
            if (i_select_add) begin : add_bit
                assign o_result[i] = i_data_a[i] ^ i_data_b[i];
            end else begin : and_bit
                assign o_result[i] = i_data_a[i] & i_data_b[i];
            end
        end
    endgenerate
endmodule
module AssertionsImmediateExample (
    input int i_value,
    input int i_min_limit,
    output bit o_assertion_pass
);
    bit pass_flag = 1;
    always_comb begin
        pass_flag = 1;
        if (i_value < i_min_limit) begin
            assert (1==0) else $error("Value %0d is below minimum limit %0d", i_value, i_min_limit);
            pass_flag = 0;
        end else begin
            assert (1==1);
            pass_flag = 1;
        end
    end
    assign o_assertion_pass = pass_flag;
endmodule
module AssertionsConcurrentExample (
    input bit clk,
    input bit reset,
    input bit i_start_op,
    input bit i_op_done,
    output bit o_dummy_out
);
    property p_start_followed_by_done;
        @(posedge clk) disable iff (reset)
        i_start_op |=> ##[1:5] i_op_done;
    endproperty
    assert property (p_start_followed_by_done);
    assign o_dummy_out = i_start_op && i_op_done;
endmodule
module StringTypeOpsExample (
    input string i_input_string,
    input int i_sub_start,
    input int i_sub_len,
    output int o_string_length,
    output string o_substring_result,
    output bit o_starts_with_data
);
    string temp_str;
    int str_len;
    string sub_str;
    bit starts_with_data_reg = 0;
    always_comb begin
        temp_str = i_input_string;
        str_len = temp_str.len();
        sub_str = "";
        if (i_sub_start >= 0 && i_sub_len >= 0 && (i_sub_start + i_sub_len) <= str_len) begin
            sub_str = temp_str.substr(i_sub_start, i_sub_len);
        end
        starts_with_data_reg = (temp_str.substr(0, 4) == "data");
    end
    assign o_string_length = str_len;
    assign o_substring_result = sub_str;
    assign o_starts_with_data = starts_with_data_reg;
endmodule
module CastingConversionsExample (
    input int i_int_val,
    input real i_real_val,
    input bit [31:0] i_bv_val,
    output byte o_byte_val,
    output int o_int_from_real,
    output real o_real_from_int,
    output longint o_longint_from_bv
);
    byte byte_res;
    int int_res;
    real real_res;
    longint longint_res;
    always_comb begin
        byte_res = $cast(byte, i_int_val);
        int_res = $cast(int, i_real_val);
        real_res = $cast(real, i_int_val);
        longint_res = $cast(longint, i_bv_val);
    end
    assign o_byte_val = byte_res;
    assign o_int_from_real = int_res;
    assign o_real_from_int = real_res;
    assign o_longint_from_bv = longint_res;
endmodule
module AlwaysLatchExample (
    input bit i_enable,
    input bit [15:0] i_data,
    output bit [15:0] o_q
);
    logic [15:0] latch_q;
    always_latch begin
        if (i_enable) begin
            latch_q <= i_data;
        end
    end
    assign o_q = latch_q;
endmodule
module StructuredPortsExample #(
    parameter type Config_t = struct packed { bit [3:0] id; int value; }
)(
    input bit clk,
    input bit reset,
    input Config_t i_config,
    output bit [3:0] o_id_reg,
    output int o_value_reg
);
    logic [3:0] id_reg = '0;
    int value_reg = 0;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            id_reg <= '0;
            value_reg <= 0;
        end else begin
            id_reg <= i_config.id;
            value_reg <= i_config.value;
        end
    end
    assign o_id_reg = id_reg;
    assign o_value_reg = value_reg;
endmodule
module ConditionalOperatorExample (
    input int i_val_a,
    input int i_val_b,
    input bit i_condition,
    output int o_result
);
    assign o_result = i_condition ? i_val_a : i_val_b;
endmodule
module PriorityUniqueCaseExample (
    input bit [2:0] i_select,
    input bit [7:0] i_data_a,
    input bit [7:0] i_data_b,
    input bit [7:0] i_data_c,
    output bit [7:0] o_result_unique,
    output bit [7:0] o_result_priority
);
    logic [7:0] temp_out_u;
    logic [7:0] temp_out_p;
    always_comb begin
        unique case (i_select)
            3'b001: temp_out_u = i_data_a;
            3'b010: temp_out_u = i_data_b;
            3'b100: temp_out_u = i_data_c;
            default: temp_out_u = 'x;
        endcase
        priority case (i_select)
            3'b001: temp_out_p = i_data_a;
            3'b01?: temp_out_p = i_data_b;
            3'b1??: temp_out_p = i_data_c;
            default: temp_out_p = '0;
        endcase
    end
    assign o_result_unique = temp_out_u;
    assign o_result_priority = temp_out_p;
endmodule
module StreamingOperatorsExample (
    input bit [31:0] i_data_word,
    output bit [7:0] o_stream_left_byte0,
    output bit [7:0] o_stream_right_byte0
);
    logic [7:0] byte0_left;
    logic [7:0] byte0_right;
    always_comb begin
        {byte0_left, 24'h0} = {>>byte{i_data_word}};
        {24'h0, byte0_right} = {<<byte{i_data_word}};
    end
    assign o_stream_left_byte0 = byte0_left;
    assign o_stream_right_byte0 = byte0_right;
endmodule
module MixedIntegerTypesExample (
    input byte i_byte_val,
    input shortint i_shortint_val,
    input int i_int_val,
    input longint i_longint_val,
    output longint o_sum
);
    longint sum_val;
    always_comb begin
        sum_val = $cast(longint, i_byte_val) + $cast(longint, i_shortint_val) + $cast(longint, i_int_val) + i_longint_val;
    end
    assign o_sum = sum_val;
endmodule
module SystemFunctionsExample (
    input int i_value,
    input bit [63:0] i_bit_vector,
    output int o_clog2_result,
    output int o_bits_result
);
    int clog2_res;
    int bits_res;
    always_comb begin
        clog2_res = $clog2(i_value);
        bits_res = $bits(i_bit_vector);
    end
    assign o_clog2_result = clog2_res;
    assign o_bits_result = bits_res;
endmodule
module NumberLiteralsExample (
    input bit [7:0] i_unsigned_in,
    input signed [7:0] i_signed_in,
    output bit [15:0] o_unsigned_concat,
    output signed [15:0] o_signed_concat
);
    bit [7:0] hex_lit = 8'hAB;
    int dec_lit = 123;
    bit [7:0] bin_lit = 8'b1100_1100;
    signed [7:0] oct_lit_signed = 8'o277;
    always_comb begin
        o_unsigned_concat = {i_unsigned_in, hex_lit};
        o_signed_concat = $signed({i_signed_in, oct_lit_signed});
    end
endmodule
module ArrayIndexingPartSelectsExample (
    input bit [63:0] i_qword,
    input bit [2:0] i_byte_idx,
    input bit [5:0] i_bit_start,
    input bit [5:0] i_width,
    output bit [7:0] o_byte,
    output bit [63:0] o_part_select_var
);
    logic [63:0] temp_part_select;
    always_comb begin
        o_byte = i_qword[i_byte_idx * 8 +: 8];
        temp_part_select = 'x;
        if (i_bit_start + i_width <= 64 && i_width > 0) begin
             temp_part_select = i_qword[i_bit_start +: i_width];
        end
    end
    assign o_part_select_var = temp_part_select;
endmodule
module InterfaceMasterExample (
    data_bus_if.master bus,
    input bit clk,
    input bit reset,
    input bit [31:0] i_addr,
    input bit [31:0] i_data,
    input bit i_write_req,
    output bit o_busy_in
);
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            bus.clk <= 0;
            bus.reset <= 0;
            bus.addr <= '0;
            bus.data <= '0;
            bus.write_en <= 0;
            bus.read_en <= 0;
        end else begin
            bus.clk <= clk;
            bus.reset <= reset;
            if (i_write_req) begin
                bus.addr <= i_addr;
                bus.data <= i_data;
                bus.write_en <= 1;
                bus.read_en <= 0;
            end else begin
                bus.write_en <= 0;
                bus.read_en <= 0;
            end
        end
    end
    assign o_busy_in = bus.busy;
endmodule
module InterfaceSlaveExample (
    data_bus_if.slave bus,
    input bit clk,
    input bit reset,
    input bit i_busy_out,
    output bit [31:0] o_addr_in,
    output bit [31:0] o_data_in,
    output bit o_write_en_in,
    output bit o_read_en_in
);
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            bus.busy <= 0;
        end else begin
            bus.busy <= i_busy_out;
        end
    end
    assign o_addr_in = bus.addr;
    assign o_data_in = bus.data;
    assign o_write_en_in = bus.write_en;
    assign o_read_en_in = bus.read_en;
endmodule
module ShortRealExample (
    input real i_real_a,
    input shortreal i_shortreal_b,
    output real o_real_sum,
    output shortreal o_shortreal_prod
);
    real sum_val;
    shortreal prod_val;
    always_comb begin
        sum_val = i_real_a + $cast(real, i_shortreal_b);
        prod_val = i_shortreal_b * 3.5;
    end
    assign o_real_sum = sum_val;
    assign o_shortreal_prod = prod_val;
endmodule
module LetConstructExample (
    input int i_x,
    input int i_y,
    output int o_result
);
    let square(z) = z * z;
    int res_val;
    always_comb begin
        res_val = square(i_x) + square(i_y);
    end
    assign o_result = res_val;
endmodule
module EnumLogicExample (
    input logic [1:0] i_mode_select,
    output logic [3:0] o_mode_vector
);
    typedef enum logic [3:0] { MODE_A = 4'b1000, MODE_B = 4'b0100, MODE_C = 4'b0010, MODE_D = 4'b0001 } Mode_e;
    Mode_e current_mode;
    always_comb begin
        case (i_mode_select)
            2'b00: current_mode = MODE_A;
            2'b01: current_mode = MODE_B;
            2'b10: current_mode = MODE_C;
            default: current_mode = MODE_D;
        endcase
    end
    assign o_mode_vector = current_mode;
endmodule
module SignedArithmeticOpsExample (
    input signed int i_val_a,
    input signed int i_val_b,
    output signed int o_sum,
    output signed int o_diff,
    output signed longint o_product
);
    signed longint product_res;
    always_comb begin
        product_res = $signed($cast(longint, i_val_a) * $cast(longint, i_val_b));
    end
    assign o_sum = i_val_a + i_val_b;
    assign o_diff = i_val_a - i_val_b;
    assign o_product = product_res;
endmodule
module ArrayReductionMethodsExample (
    input bit [15:0] i_data_vec,
    input bit [7:0] i_data_arr [0:3],
    output bit o_vec_and,
    output bit o_vec_or,
    output bit o_vec_xor,
    output bit o_arr_and,
    output bit o_arr_or,
    output bit o_arr_xor
);
    logic [31:0] combined_arr_bits;
    always_comb begin
        o_vec_and = i_data_vec.and();
        o_vec_or = i_data_vec.or();
        o_vec_xor = i_data_vec.xor();
        combined_arr_bits = {i_data_arr[0], i_data_arr[1], i_data_arr[2], i_data_arr[3]};
        o_arr_and = combined_arr_bits.and();
        o_arr_or = combined_arr_bits.or();
        o_arr_xor = combined_arr_bits.xor();
    end
endmodule
module SliceConcatenationExample (
    input bit [63:0] i_qword_in,
    input bit [15:0] i_hword_in,
    output bit [63:0] o_qword_out
);
    logic [63:0] temp_qword;
    always_comb begin
        temp_qword = {i_qword_in[63:48], i_hword_in, i_qword_in[31:16], i_qword_in[15:0]};
    end
    assign o_qword_out = temp_qword;
endmodule
module LogicalRelationalOpsExample (
    input int i_x,
    input int i_y,
    input bit i_flag,
    output bit o_logical_and,
    output bit o_logical_or,
    output bit o_logical_not,
    output bit o_equal,
    output bit o_not_equal,
    output bit o_greater_than,
    output bit o_less_than
);
    always_comb begin
        o_logical_and = i_flag && (i_x > i_y);
        o_logical_or = i_flag || (i_x == i_y);
        o_logical_not = !i_flag;
        o_equal = (i_x == i_y);
        o_not_equal = (i_x != i_y);
        o_greater_than = (i_x > i_y);
        o_less_than = (i_x < i_y);
    end
endmodule
module ShiftOperatorsExample (
    input bit [15:0] i_data_unsigned,
    input signed bit [15:0] i_data_signed,
    input int i_shift_amount,
    output bit [15:0] o_left_shift_u,
    output bit [15:0] o_logic_right_shift_u,
    output signed bit [15:0] o_left_shift_s,
    output signed bit [15:0] o_logic_right_shift_s,
    output signed bit [15:0] o_arith_right_shift_s
);
    always_comb begin
        o_left_shift_u = i_data_unsigned << i_shift_amount;
        o_logic_right_shift_u = i_data_unsigned >> i_shift_amount;
        o_left_shift_s = i_data_signed << i_shift_amount;
        o_logic_right_shift_s = $signed($unsigned(i_data_signed) >> i_shift_amount);
        o_arith_right_shift_s = i_data_signed >>> i_shift_amount;
    end
endmodule
