module SynchronousMemory (
    input logic [4:0] read_address,
    output logic [7:0] read_data,
    input logic clk,
    input logic rst,
    input logic [4:0] write_address,
    input logic write_en,
    input logic [7:0] write_data
);
    logic [7:0] mem [0:31];
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            read_data <= 8'h0;
        end else begin
            if (write_en) begin
                mem[write_address] <= write_data;
            end
            read_data <= mem[read_address];
        end
    end
endmodule

