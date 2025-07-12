typedef class CyclicA;
typedef class CyclicB;
class CyclicA;
    int a_prop;
    CyclicB b_inst;
    function new(int val_a);
        a_prop = val_a;
    endfunction
endclass

class CyclicB;
    int b_prop;
    CyclicA a_inst;
    function new(int val_b);
        b_prop = val_b;
    endfunction
endclass

module cyclic_class_module (
    input logic en,
    input int val_a_in,
    input int val_b_in,
    output logic inst_a_en,
    output logic inst_b_en,
    output logic [31:0] total_sum
);
    CyclicA inst_a;
    always_comb begin
        if (en) begin
            inst_a = new(val_a_in);
            inst_a_en = 1;
            inst_a.b_inst = new(val_b_in);
            inst_b_en = 1;
            inst_a.b_inst.a_inst = inst_a;
            total_sum = inst_a.a_prop + inst_a.b_inst.b_prop;
        end else begin
            inst_a = null;
            total_sum = 0;
            inst_a_en = 0;
            inst_b_en = 0;
        end
    end
endmodule

