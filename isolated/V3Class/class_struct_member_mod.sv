module class_struct_member_mod (
    input logic [15:0] struct_in,
    output logic [7:0] struct_f1_out
);
    typedef struct packed {
        logic [7:0] f1;
        logic [7:0] f2;
    } my_inner_struct_t;
    class ClassWithStruct;
        my_inner_struct_t member_struct;
        function new();
            member_struct.f1 = 8'h00;
            member_struct.f2 = 8'h00;
        endfunction
        task set_fields(input logic [15:0] val);
            member_struct = val;
        endtask
        function logic [7:0] get_f1();
            return member_struct.f1;
        endfunction
    endclass
    ClassWithStruct inst;
    logic [7:0] temp_f1;
    always_comb begin
        inst = new();
        inst.set_fields(struct_in);
        temp_f1 = inst.get_f1();
    end
    assign struct_f1_out = temp_f1;
endmodule

