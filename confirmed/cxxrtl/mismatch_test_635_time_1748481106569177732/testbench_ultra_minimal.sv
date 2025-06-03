// Ultra-minimal testbench with clock handling
`include "top_ultra_minimal.sv"

module top;
    logic [95:0] clkin_data;
    logic [191:0] in_data;
    logic [7:0] inj_param_out_547;

    topi dut (
        .clkin_data(clkin_data),
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

        // Initialize clkin_data from file
        fd = $fopen("input_clkin_data.hex", "r");
        if (fd == 0) begin
            $display("Error: Unable to open input_clkin_data.hex");
            $finish;
        end
        status = $fgets(line, fd);
        status = $sscanf(line, "%h", clkin_data);
        $fclose(fd);

        // Clock toggling to reproduce the timing behavior
        repeat (10) begin
            clkin_data = 0;
            #5;
            clkin_data = 1;
            #5;
        end

        // Allow settling
        #10;

        // Write output
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
