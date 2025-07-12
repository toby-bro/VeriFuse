typedef enum {
    RED = 0,
    GREEN = 1,
    BLUE = 2
} color_e;
module ModuleEnumInitializer (
    input int in_val
);
    color_e current_color;
    always_comb begin
        current_color = color_e'(in_val % 3);
    end
    assign out_color = current_color;
endmodule

