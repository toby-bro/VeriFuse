module macro_redefinition_check (
    input logic redefine_en,
    output int result_out
);
    `define REDEF_NUM 10
    `define REDEF_NUM 20
    localparam int NUM_VAL = `REDEF_NUM;
    assign result_out = redefine_en ? NUM_VAL : 0;
endmodule

