module SequentialAndParallelBlocks (
    input wire [7:0] data_in_pb,
    input wire start_sig,
    output logic [7:0] result_join,
    output logic [7:0] result_join_any,
    output logic [7:0] result_join_none,
    output logic [7:0] result_seq
);
    always @(posedge start_sig) begin
        automatic int local_var = 1;
        begin
            result_seq = data_in_pb + local_var - 1;
        end
        fork
            result_join = data_in_pb + 1;
            result_join = (data_in_pb + 1) & 8'hFF;
        join
        fork
            result_join_any = data_in_pb + 2;
            result_join_any = (data_in_pb + 2) * 3;
        join_any
        fork
            result_join_none = data_in_pb + 4;
            result_join_none = (data_in_pb + 4) | 8'hAA;
        join_none
    end
endmodule

