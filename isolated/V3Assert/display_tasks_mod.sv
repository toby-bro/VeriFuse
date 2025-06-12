module display_tasks_mod (
    input logic trigger_disp,
    output logic disp_out
);
    always @(trigger_disp) begin
        if (trigger_disp) begin
            $info("This is an info message");
            $warning("This is a warning message");
            $error("This is an error message");
            $fatal(1, "This is a fatal message");
            $display("This is a display message");
            $write("This is a write message\n");
        end
    end
    assign disp_out = trigger_disp;
endmodule

