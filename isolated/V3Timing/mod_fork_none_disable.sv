module mod_fork_none_disable (
    input logic start,
    input logic enable,
    output logic out1,
    output logic out2,
    output logic out_done
);
    initial begin
    out1 = 1'b0;
    out2 = 1'b0;
    out_done = 1'b0;
    wait(start);
    fork : my_fork
        begin : branch_a
            #5 out1 = 1'b1;
        end
        begin : branch_b
            @(posedge enable);
            if (!enable) disable fork;
            else out2 = 1'b1;
        end
    join_none
    out_done = 1'b1;
    end
endmodule

