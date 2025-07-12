module specify_conditional (
    input wire a,
    input wire b,
    input wire sel,
    output wire y
);
    assign y = sel ? a : b;
    specify
        if (sel) (a => y) = 1;
        if (!sel) (b => y) = 2;
        ifnone (a => y) = 3;
    endspecify
endmodule

