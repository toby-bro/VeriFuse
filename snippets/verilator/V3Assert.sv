module assert_property_mod(
    input logic clk,
    input logic reset_n,
    input logic req,
    input logic ack,
    input logic [7:0] data_in,
    output logic [7:0] prop_out
);
    // Assert: Request-acknowledge protocol - ack should follow req within 3 cycles
    property p_req_ack_protocol;
        @(posedge clk) disable iff (!reset_n)
        req && !ack |-> ##1 ack or ##2 ack or ##3 ack;
    endproperty
    assert property (p_req_ack_protocol) else $error("Request not acknowledged within 3 cycles");

    // Assert: Data stability - data must be stable while req is high
    property p_data_stability;
        @(posedge clk) disable iff (!reset_n)
        req && !ack |-> $stable(data_in);
    endproperty
    assert property (p_data_stability) else $error("Data changed while request pending");

    // Procedural assert: Valid data range
    always @(posedge clk) begin
        if (reset_n && req) begin
            assert (data_in != 8'hXX && data_in != 8'hZZ) 
                else $error("Invalid data during request: %h", data_in);
        end
    end

    assign prop_out = ack ? data_in : 8'h00;
endmodule
module cover_property_mod(
    input logic clk,
    input logic reset_n,
    input logic req,
    input logic ack,
    input logic busy,
    input logic error,
    output logic cover_out
);
    // Cover: Track different system states
    property p_cover_req_without_ack;
        @(posedge clk) disable iff (!reset_n)
        req && !ack;
    endproperty
    cover property (p_cover_req_without_ack);

    // Cover: Back-to-back requests
    property p_cover_back_to_back_req;
        @(posedge clk) disable iff (!reset_n)
        req ##1 req;
    endproperty
    cover property (p_cover_back_to_back_req);

    // Cover: Error conditions
    property p_cover_error_during_req;
        @(posedge clk) disable iff (!reset_n)
        req && error;
    endproperty
    cover property (p_cover_error_during_req);

    // Procedural cover: Track busy periods
    always @(posedge clk) begin
        if (reset_n) begin
            cover (busy && req) $display("Covered: System busy during request");
            cover (ack && !req) $display("Covered: Unexpected acknowledge");
        end
    end

    assign cover_out = req || ack || busy;
endmodule
module assume_property_mod (
    input logic clk,
    input logic [1:0] prio_level,
    input logic req,
    input logic reset_n,
    input logic valid_data,
    output logic assume_out
);
    property p_assume_no_req_during_reset;
        @(posedge clk) !reset_n |-> !req;
    endproperty
    assume property (p_assume_no_req_during_reset);
    property p_assume_valid_data_with_req;
        @(posedge clk) disable iff (!reset_n)
        req |-> valid_data;
    endproperty
    assume property (p_assume_valid_data_with_req);
    property p_assume_rare_high_priority;
        @(posedge clk) disable iff (!reset_n)
        req && (prio_level == 2'b11) |-> ##[5:10] !(req && (prio_level == 2'b11));
    endproperty
    assume property (p_assume_rare_high_priority);
    always @(posedge clk) begin
        if (reset_n) begin
            assume property (@(posedge clk) req ##1 req ##1 req |-> ##1 !req);
        end
    end
    assign assume_out = req && valid_data;
endmodule
module restrict_property_mod(
    input logic clk,
    input logic reset_n,
    input logic debug_mode,
    input logic test_mode,
    input logic restrict_cond,
    output logic restrict_out
);
    // Restrict: In formal verification, limit scenarios to debug mode only
    property p_restrict_debug_only;
        @(posedge clk) disable iff (!reset_n)
        1'b1 |-> debug_mode;
    endproperty
    restrict property (p_restrict_debug_only);

    // Restrict: Exclude test mode from formal analysis
    property p_restrict_no_test_mode;
        @(posedge clk) disable iff (!reset_n)
        !test_mode;
    endproperty
    restrict property (p_restrict_no_test_mode);

    assign restrict_out = restrict_cond && debug_mode && !test_mode;
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
        unique if (sel1) begin
            internal_out = 1;
        end else if (sel2) begin
            internal_out = 2;
        end else begin
            internal_out = 3;
        end
        unique0 if (sel1 && sel2) begin
            internal_out = 4;
        end else if (sel2 && sel3) begin
            internal_out = 5;
        end
    end
    assign if_pragma_out = internal_out;
endmodule
// Individual case statement modules for synthesis testing
module case_full_parallel_mod (
    output logic [4:0] internal_out,
    input logic [1:0] case_expr
);
    always @* begin
        (* full, parallel *)
        case (case_expr)
            2'b00: internal_out = 1;
            2'b01: internal_out = 2;
            2'b10: internal_out = 3;
            default: internal_out = 4;
        endcase
    end
endmodule

module case_priority_overlapping_mod (
    output logic [4:0] internal_out,
    input logic [1:0] case_expr
);
    always @* begin
        priority casez (case_expr)
            2'b1?: internal_out = 5;
            2'b?1: internal_out = 6;  // Overlaps with 2'b11 from above - violates priority
            2'b0?: internal_out = 7;
            2'b?0: internal_out = 8;  // Overlaps with 2'b10 from above - violates priority
            default: internal_out = 9;
        endcase
    end
endmodule

module case_unique0_violating_mod (
    output logic [4:0] internal_out,
    input logic [1:0] case_expr
);
    always @* begin
        unique0 casez (case_expr)
            2'b1?: internal_out = 8;
            2'b11: internal_out = 9;  // Overlaps with above - violates unique constraint
            2'b?1: internal_out = 10; // Also overlaps - multiple violations
            2'b00: internal_out = 11; // This one is okay
        endcase
    end
endmodule

module case_full_simple_mod (
    output logic [4:0] internal_out,
    input logic [1:0] case_expr
);
    always @* begin
        (* full *)
        case (case_expr)
            2'b00: internal_out = 10;
            2'b01: internal_out = 11;
            2'b10: internal_out = 12;
            default: internal_out = 13;
        endcase
    end
endmodule

module case_parallel_simple_mod (
    output logic [4:0] internal_out,
    input logic [3:0] case_inside_val
);
    always @* begin
        (* parallel *)
        case (case_inside_val)
            4'd0, 4'd1: internal_out = 14;
            4'd2, 4'd3: internal_out = 15;
            default: internal_out = 18;
        endcase
    end
endmodule

module case_unique_inside_overlapping_mod (
    output logic [4:0] internal_out,
    input logic [3:0] case_inside_val,
    input logic [3:0] range_start,
    input logic [3:0] range_end
);
    always @* begin
        unique case (case_inside_val)
            case_inside_val inside {[range_start:range_end]}: internal_out = 16;
            case_inside_val inside {4'd0, 4'd1, 4'd2}: internal_out = 17;  // May overlap with range above
            case_inside_val inside {4'd8, 4'd9}: internal_out = 18;
            case_inside_val inside {[4'd7:4'd10]}: internal_out = 19;  // Overlaps with above range
            case_inside_val inside {4'd15}: internal_out = 20;  // May overlap with first range
            default: internal_out = 21;  // Having default with unique can cause issues
        endcase
    end
endmodule

module case_unique0_inside_no_default_mod (
    output logic [4:0] internal_out,
    input logic [3:0] case_inside_val
);
    always @* begin
        unique0 case (case_inside_val)
            case_inside_val inside {4'd10, 4'd11}: internal_out = 19;
            case_inside_val inside {4'd11, 4'd12}: internal_out = 20;  // 4'd11 overlaps - violates unique0
            case_inside_val inside {[4'd10:4'd13]}: internal_out = 21;  // Massive overlap with both above
            case_inside_val inside {4'd14, 4'd15}: internal_out = 22;
            case_inside_val inside {4'd15}: internal_out = 23;  // 4'd15 overlaps with above
            // No default case - this can cause synthesis issues with unique0
        endcase
    end
endmodule

module case_priority_casex_complex_mod (
    output logic [4:0] internal_out,
    input logic [1:0] case_expr,
    input logic [3:0] case_inside_val
);
    always @* begin
        priority casex ({case_expr, case_inside_val[1:0]})
            4'b1???: internal_out = 24;
            4'b?1??: internal_out = 25;  // Overlaps with above for 4'b11??
            4'b??1?: internal_out = 26;  // More overlaps
            4'b???1: internal_out = 27;  // Even more overlaps
            4'b0000: internal_out = 28;  // This specific case overlaps with multiple above
            default: internal_out = 29;
        endcase
    end
endmodule

module case_unique_casez_reordered_mod (
    output logic [4:0] internal_out,
    input logic [1:0] case_expr,
    input logic [3:0] case_inside_val
);
    always @* begin
        unique casez ({case_expr[0], case_inside_val[3:2], case_expr[1]})
            4'b1?0?: internal_out = 30;
            4'b?101: internal_out = 31;  // May overlap depending on values
            4'b0?1?: internal_out = 32;
            4'b1?1?: internal_out = 33;  // Overlaps with first case when middle bits are anything
            4'b?111: internal_out = 34;  // Complex overlap pattern
        endcase
    end
endmodule

// Top-level module that instantiates all case modules
module case_pragmas_mod (
    output logic case_pragma_out,
    input logic [1:0] case_expr,
    input logic [3:0] case_inside_val,
    input logic [3:0] range_start,
    input logic [3:0] range_end
);
    logic [4:0] out1, out2, out3, out4, out5, out6, out7, out8, out9;
    logic [4:0] combined_out;

    // Instantiate all case modules
    case_full_parallel_mod u1 (
        .internal_out(out1),
        .case_expr(case_expr)
    );

    case_priority_overlapping_mod u2 (
        .internal_out(out2),
        .case_expr(case_expr)
    );

    case_unique0_violating_mod u3 (
        .internal_out(out3),
        .case_expr(case_expr)
    );

    case_full_simple_mod u4 (
        .internal_out(out4),
        .case_expr(case_expr)
    );

    case_parallel_simple_mod u5 (
        .internal_out(out5),
        .case_inside_val(case_inside_val)
    );

    case_unique_inside_overlapping_mod u6 (
        .internal_out(out6),
        .case_inside_val(case_inside_val),
        .range_start(range_start),
        .range_end(range_end)
    );

    case_unique0_inside_no_default_mod u7 (
        .internal_out(out7),
        .case_inside_val(case_inside_val)
    );

    case_priority_casex_complex_mod u8 (
        .internal_out(out8),
        .case_expr(case_expr),
        .case_inside_val(case_inside_val)
    );

    case_unique_casez_reordered_mod u9 (
        .internal_out(out9),
        .case_expr(case_expr),
        .case_inside_val(case_inside_val)
    );

    // Combine all outputs with complex logic
    always @* begin
        combined_out = out1 ^ out2 ^ out3 ^ out4 ^ out5 ^ out6 ^ out7 ^ out8 ^ out9;
    end

    assign case_pragma_out = combined_out[0] ^ combined_out[4] ^ (|combined_out[3:1]);
endmodule
module procedural_assert_mod(
    input logic clk,
    input logic reset_n,
    input logic enable,
    input logic [3:0] counter,
    input logic overflow,
    output logic proc_assert_out
);
    // Improved procedural assertions with boolean logic only
    always @(posedge clk) begin
        if (reset_n) begin
            // Assert: Counter should not exceed maximum when not in overflow mode
            assert (!(!overflow && enable) || (counter <= 4'hE)) 
                else $error("Counter exceeded limit without overflow flag: %d", counter);
            
            // Assert: Overflow flag should be set when counter reaches maximum
            assert (!(counter == 4'hF) || overflow) 
                else $warning("Counter at maximum but overflow not set");
            
            // Assert: Enable should be low when overflow occurs
            assert (!overflow || !enable)
                else $error("Enable still high during overflow");
        end
    end
    
    // Assert: Reset behavior - during reset, counter and overflow should be zero
    always @(posedge clk) begin
        assert (reset_n || (counter == 4'h0 && !overflow))
            else $error("Improper reset behavior");
    end

    // Property-based assertion for temporal relationship
    property p_overflow_recovery;
        @(posedge clk) disable iff (!reset_n)
        $rose(overflow) |-> ##1 (counter == 4'h0) or ##2 (counter == 4'h0);
    endproperty
    assert property (p_overflow_recovery)
        else $error("Counter did not reset after overflow");

    assign proc_assert_out = enable && !overflow;
endmodule
