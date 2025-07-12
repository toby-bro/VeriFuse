module ModuleForwardTypedefs (
    input logic dummy_in,
    output logic dummy_out
);
    typedef class ForwardedClass;
    class ForwardedClass;
        int val;
        function new (int v); val = v; endfunction
    endclass
    ForwardedClass cls_h;
    always_comb begin
        cls_h = new(10);
        if (cls_h != null)
            dummy_out = cls_h.val > 0;
        else
            dummy_out = dummy_in;
    end
endmodule

