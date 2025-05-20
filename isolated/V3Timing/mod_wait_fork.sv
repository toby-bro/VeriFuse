module mod_wait_fork (
    input logic start,
    input logic trigger,
    output logic out
);
    initial begin
    out = 1'b0;
    wait(start);
    fork : my_async_fork
        begin : async_branch
            #10 out = 1'b1;
        end
    join_none
    wait(trigger);
    wait fork;
    out = out + 1;
    end
endmodule

