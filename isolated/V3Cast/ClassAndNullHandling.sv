module ClassAndNullHandling (
    input logic create_obj,
    input logic pass_derived,
    input int method_arg,
    output int method_result,
    output int class_op_result
);
    class Base;
        int data = 10;
        virtual function int get_data();
            return data;
        endfunction
        function void set_data(int val);
            data = val;
        endfunction
    endclass
    class Derived extends Base;
        int derived_data = 20;
        function int get_data(); 
            return data + derived_data;
        endfunction
    endclass
    Base base_inst;
    Derived derived_inst;
    Base obj_ref; 
    Base cond_result_wire; 
    always_comb begin
        base_inst = null;
        derived_inst = null;
        obj_ref = null;
        cond_result_wire = null;
        method_result = -1; 
        class_op_result = -2; 
        if (create_obj) begin
            base_inst = new(); 
            derived_inst = new(); 
            obj_ref = pass_derived ? derived_inst : base_inst;
            cond_result_wire = pass_derived ? derived_inst : base_inst;
        end
        if (obj_ref != null) begin
            method_result = obj_ref.get_data(); 
            obj_ref.set_data(method_arg); 
        end
        if (cond_result_wire != null) begin
            class_op_result = cond_result_wire.get_data();
        end
    end
endmodule

