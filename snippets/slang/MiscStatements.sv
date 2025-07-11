module disable_stmt_mod (
    input logic clk,
    input logic enable_in,
    output logic done_out
);
    static logic temp_var;
    task my_task();
        @(posedge clk);
        temp_var = 1;
    endtask
    always @(posedge clk) begin : my_block_label
        automatic logic block_var = 0;
        if (enable_in) begin
            my_task();
            disable my_task;
            disable my_block_label;
            done_out = 1;
        end else begin
            done_out = 0;
        end
    end
endmodule
module variable_decl_mod (
    input logic data_in,
    output logic result_out
);
    static logic [7:0] module_static_var = 8'hAA;
    always_comb begin
        automatic logic proc_auto_var;
        static logic [7:0] block_var = 8'hBB;
        logic [7:0] another_block_var;
        proc_auto_var = data_in;
        another_block_var = {7'b0, data_in} + 1;
        result_out = block_var[0] ^ another_block_var[0] ^ module_static_var[7];
    end
endmodule
module expression_stmt_mod (
    input logic [3:0] in1,
    input logic [3:0] in2,
    output logic [3:0] out1,
    output logic [3:0] out2,
    output logic dummy_void
);
    static logic [3:0] temp1, temp2;
    static int count;
    static logic void_result = 0;
    class my_class;
        int val;
        function new(int v); val = v; endfunction
        function int get_val(); return val; endfunction
    endclass
    function logic [3:0] my_function(logic [3:0] val);
        return val + 1;
    endfunction
    always_comb begin
        temp1 = in1;
        temp2 <= in2;
        count++;
        --count;
        out1 = my_function(temp1);
        void'(my_function(in2)); 
        begin
            automatic my_class obj = new(in1);
            out2 = obj.get_val();
        end
    end
        assign dummy_void = void_result; 
endmodule
module timed_stmt_mod (
    input logic clk,
    input logic enable,
    output logic data_out
);
    static logic temp_data = 0;
    always @(posedge clk) begin
        if (enable) begin
            @(posedge clk) temp_data = ~temp_data;
        end
    end
    assign data_out = temp_data;
endmodule
module immediate_assert_mod (
    input logic clk,
    input logic condition1,
    input logic condition2,
    output logic status_ok
);
    static logic internal_status = 1;
    task my_action_task();
        internal_status = 1;
    endtask
    task my_fail_task();
        internal_status = 0;
    endtask
    always @(posedge clk) begin
        assert (condition1 == 1) my_action_task();
        else my_fail_task();
        assume (condition2 inside {0, 1});
        cover (condition1 && condition2) my_action_task();
        assert final (condition1) my_action_task();
        else my_fail_task();
        assume final (condition2) my_action_task();
        assert #0 (condition1) my_action_task(); 
        status_ok = internal_status;
    end
endmodule
module concurrent_assert_mod (
    input logic clk,
    input logic reset,
    input logic req,
    input logic gnt,
    output logic assert_fail
);
    static logic fail_flag = 0;
    property req_gnt_prop;
        @(posedge clk) disable iff (reset) req |=> ##1 gnt;
    endproperty
    task assert_fail_task();
        fail_flag = 1;
    endtask
    task assert_pass_task();
        fail_flag = 0;
    endtask
    always @(posedge clk) begin
        assert property (req_gnt_prop) assert_pass_task();
        else assert_fail_task();
        assume property (@(posedge clk) req);
        cover property (@(posedge clk) req && gnt);
    end
    assign assert_fail = fail_flag;
endmodule
module fork_wait_disable_mod (
    input logic clk,
    input logic start_in,
    output logic done_out
);
    static logic task1_done = 0;
    static logic task2_done = 0;
    static logic inner_block_done = 0;
    task t1();
        @(posedge clk);
        task1_done = 1;
    endtask
    task t2();
        @(posedge clk);
        task2_done = 1;
    endtask
    always @(posedge clk) begin
        if (start_in) begin
            task1_done = 0;
            task2_done = 0;
            inner_block_done = 0;
            fork
                t1();
                t2();
                begin : inner_block
                    @(posedge clk);
                    inner_block_done = 1;
                end
            join_none
        end
    end
    always @(posedge clk) begin
        if (start_in) begin
            fork
                @(posedge clk);
                @(posedge clk);
                disable fork;
            join
            fork
                @(posedge clk);
                @(posedge clk);
                wait fork;
            join
            done_out = task1_done && task2_done && inner_block_done;
        end else begin
            done_out = 0;
        end
    end
endmodule
module wait_stmt_mod (
    input logic clk,
    input logic [1:0] state,
    output logic triggered
);
    static logic internal_trigger = 0;
    always @(posedge clk) begin
        wait (state == 2'b10) internal_trigger = 1;
    end
    assign triggered = internal_trigger;
endmodule
module wait_order_mod (
    input logic clk,
    input logic start,
    output logic ordered_ok
);
    event event1, event2, event3;
    static logic status = 0;
    task order_pass_task(); status = 1; endtask
    task order_fail_task(); status = 0; endtask
    always @(posedge clk) begin
        if (start) begin
            status = 0;
            -> event1;
            -> event3;
            -> event2;
            wait_order (event1, event2, event3) order_pass_task();
            else order_fail_task();
        end
    end
    assign ordered_ok = status;
endmodule
module event_trigger_mod (
    input logic clk,
    input logic trigger_in,
    output logic event_occured
);
    event my_event;
    static logic event_triggered = 0;
    always @(posedge clk) begin
        if (trigger_in) begin
            -> my_event; 
        end else begin
            ->> @(posedge clk) my_event; 
        end
    end
    always @(my_event) begin
        event_triggered = ~event_triggered;
    end
    assign event_occured = event_triggered;
endmodule
module procedural_assign_mod (
    input logic [7:0] value_in,
    input logic force_en,
    input logic release_en,
    output logic [7:0] data_out
);
    static logic [7:0] my_reg;
    static logic [15:0] another_reg;
    wire [15:0] concat_net;
    wire [3:0] part_net;
    always @* begin
        if (force_en) begin
            force my_reg = value_in;
            force concat_net = {value_in, value_in + 1};
            // force part_net[2:1] = value_in[1:0]; // illegal procedural assignment to net, removed for slang compatibility
        end else if (release_en) begin
            release my_reg;
            release concat_net;
            release part_net;
        end else begin
            my_reg = value_in + 1;
            another_reg <= {value_in, value_in};
            {another_reg[7:0], another_reg[15:8]} = {value_in, value_in + 1};
            // part_net[2:1] = value_in[1:0]; // illegal procedural assignment to net, removed for slang compatibility
        end
        data_out = my_reg;
    end
endmodule
module procedural_deassign_mod (
    input logic [7:0] value_in,
    input logic action_select, 
    output logic [7:0] data_out
);
    reg [7:0] my_var_reg;
    wire [7:0] my_var_wire;
    always @* begin
        if (action_select == 0) begin 
            my_var_reg = value_in;
            // my_var_wire = value_in; // illegal procedural assignment to net, removed for slang compatibility
        end else if (action_select == 1) begin 
            deassign my_var_reg;
        end else begin 
            release my_var_wire;
        end
        data_out = my_var_reg; 
    end
endmodule
module rand_case_mod (
    input logic [2:0] selector,
    output logic [3:0] result_out
);
    always_comb begin
        // slang does not support randcase with conditions; use case instead
        case (selector)
            0: result_out = 4'h0;
            1: result_out = 4'h1;
            2: result_out = 4'hA;
            default: result_out = 4'hF;
        endcase
    end
endmodule
module rand_sequence_mod (
    input logic start_seq,
    output logic dummy_out
);
    static logic seq_done = 0;
    always @(*) begin
        if (start_seq) begin
            // randsequence (rs_prod_A); // slang does not support randsequence, removed
            seq_done = 1;
        end else begin
            seq_done = 0;
        end
    end
    assign dummy_out = seq_done;
endmodule
checker my_checker (input logic clk, reset, req, gnt);
    property req_gnt_prop;
        @(posedge clk) disable iff (reset) req |=> ##1 gnt;
    endproperty
    assert property (req_gnt_prop);
endchecker
module procedural_checker_mod (
    input logic clk,
    input logic reset,
    input logic req,
    input logic gnt,
    output logic dummy_out
);
    always @(posedge clk) begin
        if (reset) begin
            my_checker chk_inst_reset (.*);
        end else begin
            my_checker chk_inst_active (.*);
        end
    end
    assign dummy_out = req & gnt;
endmodule
