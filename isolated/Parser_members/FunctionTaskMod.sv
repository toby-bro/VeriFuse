module FunctionTaskMod (
    input logic [7:0] data_in,
    output logic is_even
);
    function automatic bit check_even(input logic [7:0] v);
        check_even = ~v[0];
    endfunction
    task automatic dummy_task(input logic [7:0] v);
        int tmp;
        tmp = v;
    endtask
    assign is_even = check_even(data_in);
endmodule

