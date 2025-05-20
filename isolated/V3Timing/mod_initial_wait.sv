module mod_initial_wait (
    input logic start,
    input logic condition,
    output logic done
);
    initial begin
    done = 1'b0;
    wait(start);
    wait(condition);
    done = 1'b1;
    end
endmodule

