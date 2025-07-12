module builtin_macros_user (
    input logic info_en,
    output string file_line_info
);
    always_comb begin
        file_line_info = info_en ? {`__FILE__, ":", $sformatf("%0d", `__LINE__)} : "";
    end
endmodule

