module countbits_ops (
    input wire clk,
    input logic [7:0] in_d,
    input wire rst,
    output logic [3:0] cnt,
    output logic inj_is_even_1755304956898_531
);
    // BEGIN: FunctionTaskMod_ts1755304956899
    function automatic bit check_even(input logic [7:0] v);
        check_even = ~v[0];
    endfunction
    task automatic dummy_task(input logic [7:0] v);
        int tmp_ts1755304956899;
        tmp_ts1755304956899 = v;
    endtask
    assign inj_is_even_1755304956898_531 = check_even(in_d);
    // END: FunctionTaskMod_ts1755304956899

    assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule

