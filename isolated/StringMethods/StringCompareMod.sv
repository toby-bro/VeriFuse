module StringCompareMod (
    input string s1,
    input string s2,
    output int compare_result,
    output int icompare_result
);
    always @(*) begin
        compare_result = s1.compare(s2);
        icompare_result = s1.icompare(s2);
    end
endmodule

