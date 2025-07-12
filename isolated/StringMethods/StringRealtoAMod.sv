module StringRealtoAMod (
    input real val_real,
    output string s_out_real
);
    var string temp_string = ""; 
    always @(*) begin
        temp_string.realtoa(val_real);
        s_out_real = temp_string;
    end
endmodule

