// Minimal SystemVerilog testbench without timing constructs
`include "top_minimal.sv"

module top;
    logic [191:0] in_data;
    logic [7:0] inj_param_out_547;

    topi dut (
        .in_data(in_data),
        .inj_param_out_547(inj_param_out_547)
    );

    initial begin
        string line;
        int fd;
        int status;

        // Read input file
        fd = $fopen("input_in_data.hex", "r");
        if (fd == 0) begin
            $display("Error: Unable to open input_in_data.hex");
            $finish;
        end
        status = $fgets(line, fd);
        status = $sscanf(line, "%h", in_data);
        $fclose(fd);

        // Allow combinational logic to settle
        #1;

        // Write output file
        fd = $fopen("output_inj_param_out_547.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file");
            $finish;
        end
        for (int i = 7; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_param_out_547[i]);
        end
        $fwrite(fd, "\n");
        $fclose(fd);

        $finish;
    end
endmodule
