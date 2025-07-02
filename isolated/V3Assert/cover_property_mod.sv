module cover_property_mod (
    input logic ack,
    input logic busy,
    input logic clk,
    input logic error,
    input logic req,
    input logic reset_n,
    output logic cover_out
);
    property p_cover_req_without_ack;
        @(posedge clk) disable iff (!reset_n)
        req && !ack;
    endproperty
    cover property (p_cover_req_without_ack);
    property p_cover_back_to_back_req;
        @(posedge clk) disable iff (!reset_n)
        req ##1 req;
    endproperty
    cover property (p_cover_back_to_back_req);
    property p_cover_error_during_req;
        @(posedge clk) disable iff (!reset_n)
        req && error;
    endproperty
    cover property (p_cover_error_during_req);
    always @(posedge clk) begin
        if (reset_n) begin
            cover (busy && req) $display("Covered: System busy during request");
            cover (ack && !req) $display("Covered: Unexpected acknowledge");
        end
    end
    assign cover_out = req || ack || busy;
endmodule

