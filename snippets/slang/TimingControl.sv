module mod_delay_proc (
    input wire clk,
    input wire [7:0] delay_val,
    output reg [7:0] out_delay
);
    always @(posedge clk) begin
        #(delay_val) out_delay <= delay_val;
    end
endmodule
module mod_delay_net #(
    parameter int D = 5
) (
    input wire data_in,
    output wire data_out
);
    wire #(D) net_dly = data_in;
    assign data_out = net_dly;
endmodule
module mod_delay3_syntax (
    input wire data_in,
    output wire data_out
);
    wire #(1:2:3) net_dly = data_in;
    assign data_out = net_dly;
endmodule
module mod_delay3_net #(
    parameter int D1 = 1,
    parameter int D2 = 2,
    parameter int D3 = 3
) (
    input wire data_in,
    output wire data_out
);
    wire #(D1:D2:D3) net_dly = data_in;
    assign data_out = net_dly;
endmodule
module mod_onestep_delay (
    input wire data_in,
    output wire data_out
);
    assign #1step data_out = data_in;
endmodule
module mod_event_signal (
    input wire clk,
    input wire rst,
    input wire data_in,
    input wire [1:0] edge_in,
    output reg out_clk_pos,
    output reg out_rst_neg,
    output reg out_data_any,
    output reg out_edge_specific
);
    always @(posedge clk) begin
        out_clk_pos <= 1'b1;
    end
    always @(negedge rst) begin
        out_rst_neg <= 1'b1;
    end
    always @(data_in) begin
        out_data_any <= data_in;
    end
        always @(posedge edge_in) begin
            out_edge_specific <= 1'b1;
        end
endmodule
module mod_event_list (
    input wire clk,
    input wire rst,
    input wire enable,
    input wire data_in,
    output reg out_event_list
);
    always @(posedge clk or negedge rst or enable or data_in) begin
        out_event_list <= 1'b1;
    end
endmodule
module mod_event_implicit (
    input wire [3:0] data_in,
    output reg [3:0] data_out
);
    always @* begin
        data_out = data_in;
    end
endmodule
module mod_event_repeat (
    input wire clk,
    input wire [7:0] count,
    output reg toggle
);
    always @(posedge clk) begin
        repeat (count) @(posedge clk);
        toggle <= ~toggle;
    end
endmodule
module mod_event_id (
    input wire clk,
    output reg fired
);
    event my_event;
    always @(posedge clk) begin
        -> my_event;
    end
    always @(my_event) begin
        fired = ~fired;
    end
endmodule
module mod_event_posedge (
    input wire clk,
    input wire data_in,
    output reg data_out
);
    always @(posedge clk) begin
        data_out <= data_in;
    end
endmodule
module mod_delay_net_real_param (
    input wire data_in,
    output wire data_out
);
    parameter real R_PARAM = 3.14;
    wire #(R_PARAM) net_dly_param = data_in;
    assign data_out = net_dly_param;
endmodule
module mod_event_any_multibit (
    input wire clk,
    input wire [1:0] array_in,
    output logic dummy
);
    always @(array_in) begin
        dummy = ~dummy;
    end
endmodule
module mod_err_event_multibit (
    input wire clk,
    input wire [2:0] multi_bit_in,
    output logic dummy
);
    always @(posedge multi_bit_in) begin
        dummy = ~dummy;
    end
endmodule
module mod_err_event_constant (
    input wire clk,
    output logic dummy
);
    always @(posedge 1'b1) begin
        dummy = ~dummy;
    end
endmodule
module mod_err_event_iff_nonbool (
    input wire clk,
    input wire [1:0] condition_in,
    output logic dummy
);
    always @(posedge clk iff condition_in) begin
        dummy = ~dummy;
    end
endmodule
