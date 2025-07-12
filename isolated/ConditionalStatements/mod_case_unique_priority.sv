module mod_case_unique_priority (
    input bit [2:0] in_state_case,
    output bit out_priority_case,
    output bit out_unique_case
);
always_comb begin
    out_unique_case = 1'b0;
    unique case (in_state_case)
        3'd0: out_unique_case = 1'b0;
        3'd1: out_unique_case = 1'b1;
        3'd2: out_unique_case = 1'b0;
        3'd1: out_unique_case = 1'b1;
        default: out_unique_case = 1'b1;
    endcase
end
always_comb begin
    out_priority_case = 1'b0;
    priority case (in_state_case)
        3'd0: out_priority_case = 1'b0;
        3'd1: out_priority_case = 1'b1;
        3'd2: out_priority_case = 1'b0;
        3'd1: out_priority_case = 1'b1;
        default: out_priority_case = 1'b1;
    endcase
end
endmodule

