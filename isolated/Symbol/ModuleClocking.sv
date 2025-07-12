module ModuleClocking (
    input logic clk_in,
    input logic data_in,
    output logic data_out
);
    clocking cb @(posedge clk_in);
        input  data_in;
        output data_out;
    endclocking
    always_ff @(cb) begin
        data_out <= cb.data_in;
    end
endmodule

