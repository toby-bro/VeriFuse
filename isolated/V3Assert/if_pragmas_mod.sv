module if_pragmas_mod (
    input logic sel1,
    input logic sel2,
    input logic sel3,
    output logic if_pragma_out
);
    logic internal_out = 0;
    always @* begin
        internal_out = 0;
        unique if (sel1) begin
            internal_out = 1;
        end else if (sel2) begin
            internal_out = 2;
        end else begin
            internal_out = 3;
        end
        unique0 if (sel1 && sel2) begin
            internal_out = 4;
        end else if (sel2 && sel3) begin
            internal_out = 5;
        end
    end
    assign if_pragma_out = internal_out;
endmodule

