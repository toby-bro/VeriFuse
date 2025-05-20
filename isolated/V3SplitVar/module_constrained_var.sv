module module_constrained_var (
    output logic [3:0] output_cv,
    inout wire [3:0] inout_cv,
    input logic enable_cv,
    output logic [7:0] counter_cv_out,
    output logic [7:0] counter_split_out,
    input logic [3:0] input_cv
);
    logic [7:0] internal_state ;
    logic [15:0] forceable_var ;
    logic [7:0] counter_cv;
    logic [7:0] counter_split ;
    assign output_cv = input_cv;
    assign inout_cv = input_cv;
    assign counter_cv_out = counter_cv;
    assign counter_split_out = counter_split;
    always_comb begin
        if (enable_cv) begin
            counter_cv = counter_cv + 8'b1;
            internal_state = counter_cv;
            forceable_var = {counter_cv, counter_cv};
        end else begin
            counter_cv = 8'b0;
            internal_state = 8'h00;
            forceable_var = 16'h0000;
        end
        counter_split = counter_cv + 8'd10;
    end
endmodule

