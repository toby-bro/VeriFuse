module ClassAndNullHandling (
    input logic clk,
    input logic reset,
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
    
    // Use clocked logic for object creation to ensure deterministic behavior
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            base_inst = null;
            derived_inst = null;
            obj_ref = null;
            cond_result_wire = null;
        end else if (create_obj) begin
            base_inst = new(); 
            derived_inst = new(); 
            obj_ref = pass_derived ? derived_inst : base_inst;
            cond_result_wire = pass_derived ? derived_inst : base_inst;
        end else begin
            base_inst = null;
            derived_inst = null;
            obj_ref = null;
            cond_result_wire = null;
        end
    end
    
    // Separate combinational logic for outputs
    always_comb begin
        if (obj_ref != null) begin
            method_result = obj_ref.get_data();
        end else begin
            method_result = -1;
        end
        
        if (cond_result_wire != null) begin
            class_op_result = cond_result_wire.get_data();
        end else begin
            class_op_result = -2;
        end
    end
    
    // Handle method argument setting separately if needed
    always_ff @(posedge clk) begin
        if (obj_ref != null && create_obj) begin
            obj_ref.set_data(method_arg);
        end
    end
endmodule
