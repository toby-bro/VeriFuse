module assert_property_mod (
    input logic ack,
    input logic clk,
    input logic [7:0] data_in,
    input logic req,
    input logic reset_n,
    output logic [7:0] prop_out
);
    property p_req_ack_protocol;
        @(posedge clk) disable iff (!reset_n)
        req && !ack |-> ##1 ack or ##2 ack or ##3 ack;
    endproperty
    assert property (p_req_ack_protocol) else $error("Request not acknowledged within 3 cycles");
    property p_data_stability;
        @(posedge clk) disable iff (!reset_n)
        req && !ack |-> $stable(data_in);
    endproperty
    assert property (p_data_stability) else $error("Data changed while request pending");
    always @(posedge clk) begin
        if (reset_n && req) begin
            assert (data_in != 8'hXX && data_in != 8'hZZ) 
                else $error("Invalid data during request: %h", data_in);
        end
    end
    assign prop_out = ack ? data_in : 8'h00;
endmodule

