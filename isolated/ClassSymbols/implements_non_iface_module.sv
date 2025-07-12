typedef class ImplementsNonIfaceError;
class Basic;
    int data;
    function new();
        data = 5;
    endfunction
    function int getData();
        return data;
    endfunction
endclass

class ImplementsNonIfaceError extends Basic;
    int val = 1;
    function new();
        val = 2;
    endfunction
endclass

module implements_non_iface_module (
    input logic en,
    output logic implements_non_class_inst_en
);
    ImplementsNonIfaceError implements_non_class_inst;
    always_comb begin
        if (en) begin
            implements_non_class_inst = new();
            implements_non_class_inst_en = 1;
        end else begin
            implements_non_class_inst = null;
            implements_non_class_inst_en = 0;
        end
    end
endmodule

