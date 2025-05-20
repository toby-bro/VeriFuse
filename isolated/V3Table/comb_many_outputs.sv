module comb_many_outputs (
    input bit ctrl,
    output bit o1,
    output bit o4,
    input bit [7:0] val,
    output bit o5,
    output bit o7,
    output bit o2,
    output bit o3,
    output bit o0,
    output bit o6
);
    always @* begin
    o0 = ctrl & val[0];
    o1 = ctrl | val[1];
    o2 = ctrl ^ val[2];
    o3 = ~val[3];
    o4 = ctrl && val[4];
    o5 = ctrl || val[5];
    o6 = val[6];
    o7 = val[7];
      end
endmodule

