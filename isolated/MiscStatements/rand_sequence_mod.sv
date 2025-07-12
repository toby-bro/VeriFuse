module rand_sequence_mod (
    input logic start_seq,
    output logic dummy_out
);
    static logic seq_done = 0;
    always @(*) begin
        if (start_seq) begin
            seq_done = 1;
        end else begin
            seq_done = 0;
        end
    end
    assign dummy_out = seq_done;
endmodule

