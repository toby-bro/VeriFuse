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

