module mod_fork_join (
    input logic start,
    input logic in1,
    input logic in2,
    output logic out
);
    initial begin
    out = 1'b0;
    wait(start);
    fork
        begin : branch1
            #2 out = in1;
        end
        begin : branch2
            @(posedge in2);
            out = in2;
        end
    join
    out = out + 1;
    end
endmodule

