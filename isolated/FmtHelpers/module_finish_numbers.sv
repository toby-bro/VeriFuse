module module_finish_numbers (
    input bit dummy_in,
    output bit dummy_out
);
    parameter p_finish_0 = 0;
    parameter p_finish_1 = 1;
    parameter p_finish_2 = 2;
    parameter p_finish_other_3 = 3;
    parameter p_finish_large_100 = 100;
    parameter p_finish_neg_minus1 = -1;
    localparam lp_finish_0 = 0;
    localparam lp_finish_1 = 1;
    localparam lp_finish_2 = 2;
    localparam lp_finish_other_5 = 5;
    localparam lp_finish_neg_minus10 = -10;
    assign dummy_out = dummy_in;
endmodule

