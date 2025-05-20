class MySimpleClass;
      int member_int;
      logic member_logic;
      logic [63:0] member_wide;
      function new(int i, logic l, logic [63:0] w);
        member_int = i;
        member_logic = l;
        member_wide = w;
      endfunction
endclass

module ModuleWithClass (
    input logic in1,
    output logic out1
);
    MySimpleClass my_instance;
      always_comb begin
    my_instance = new(10, in1, 64'hFFFF_0000_FFFF_0000);
    out1 = my_instance.member_logic;
      end
endmodule

