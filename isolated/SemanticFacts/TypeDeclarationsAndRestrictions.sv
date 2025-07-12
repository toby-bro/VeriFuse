module TypeDeclarationsAndRestrictions (
    input wire [7:0] in_val,
    output logic [7:0] out_val
);
    typedef enum logic [1:0] {STATE_IDLE = 0, STATE_BUSY = 1, STATE_DONE = 2} my_enum_t;
    typedef struct packed {logic [3:0] field1; logic [3:0] field2;} my_struct_t;
    typedef struct {int unpacked_f1; int unpacked_f2;} my_unpacked_struct_t;
    typedef union packed {logic [7:0] byte_val; my_struct_t fields;} my_union_t;
    typedef union {longint unpacked_u_l; int unpacked_u_i;} my_unpacked_union_t;
    interface class MyInterfaceClass;
        pure virtual function int get_id();
    endclass
    typedef class ForwardClass;
    typedef interface class ForwardIfaceClass;
    typedef enum {FWD_E1} ForwardEnum;
    typedef struct packed {int field;} ForwardStruct_t;
    typedef union  packed {int field;} ForwardUnion_t;
    class ForwardClass;
        int field;
        function new(); endfunction
    endclass
    interface class ForwardIfaceClass;
        pure virtual function void dummy_func();
    endclass
    my_struct_t           s_var;
    my_unpacked_struct_t  us_var;
    my_union_t            u_var;
    my_unpacked_union_t   uu_var;
    my_enum_t             e_var;
    ForwardStruct_t       fwd_struct_var;
    ForwardUnion_t        fwd_union_var;
    ForwardEnum           fwd_enum_var;
    assign out_val = in_val;
endmodule

