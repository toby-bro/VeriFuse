module ModuleFinishStop (
    input wire enable_fs,
    input wire [7:0] status_fs,
    output reg dummy_out_fs
);
    always @* begin
        dummy_out_fs = enable_fs;
        if (enable_fs) begin
            $finish;
            $finish(status_fs); 
            $stop;
            $stop(status_fs); 
        end
    end
endmodule

