module top;
    logic out;
    logic in;
    logic in2;

    bug dut (
        .out(out),
        .in(in),
        .in2(in2)
    );


    initial begin
        string line;
        int fd;
        int status;

        in = 'h0;
        in2 = 'h0;

        #20;
        in = 'h1;
        #20;

        $display("out: %b", out);

        // Assertion to check if 'out' is 0 at the end of simulation
        assert(out == 0) else $fatal(0, "Assertion failed: 'out' is not 0 at the end of simulation");

        $finish;
    end
endmodule
