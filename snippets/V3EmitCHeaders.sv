module basic_module (
    input logic in1,
    input logic [7:0] in2,
    output logic out1,
    output int out2
);
    parameter int PARAM_INT = 10;
    parameter real PARAM_REAL = 3.14;
    parameter logic [3:0] PARAM_VEC = 4'b1010;
    logic internal_signal_a;
    int internal_signal_b;
    logic [15:0] internal_vec_c;
    logic [63:0] internal_wide_d; 
    logic [7:0] internal_signals[0:99]; 
    always_comb begin
        out1 = in1 | internal_signal_a;
        out2 = in2 + internal_signal_b + PARAM_INT;
        internal_signal_a = in2[0];
        internal_signal_b = PARAM_INT * 2;
        internal_vec_c = internal_signal_b + PARAM_VEC;
        internal_wide_d = {64{in1}} ^ {64{in2[7]}};
        for (int i = 0; i < 100; i++) begin
            internal_signals[i] = in2 + i;
        end
    end
endmodule
module enum_module (
    input logic [2:0] status_in,
    output logic [7:0] status_out
);
    typedef enum {
        STATE_IDLE,
        STATE_BUSY = 5,
        STATE_DONE = 10
    } my_local_enum_t;
    typedef enum bit [65:0] { 
        LARGE_ENUM_A = 66'd0,
        LARGE_ENUM_B = 66'd100
    } large_enum_t;
    typedef enum logic [1:0] { 
        FOUR_STATE_A = 2'b01,
        FOUR_STATE_B = 2'bx
    } four_state_enum_t;
    (* public *)
    typedef enum {
        PUBLIC_MODE_READ,
        PUBLIC_MODE_WRITE
    } public_mode_enum_t;
    my_local_enum_t current_state;
    large_enum_t large_val;
    four_state_enum_t four_state_val;
    public_mode_enum_t public_mode;
    always_comb begin
        current_state = my_local_enum_t'(status_in);
        large_val = LARGE_ENUM_A;
        four_state_val = FOUR_STATE_A;
        public_mode = PUBLIC_MODE_READ;
        case (current_state)
            STATE_IDLE: status_out = 8'h00;
            STATE_BUSY: status_out = 8'hFF;
            default:    status_out = 8'hAA;
        endcase
    end
endmodule
module unpacked_struct_module (
    input logic [15:0] data_in,
    output logic [7:0] checksum_out
);
    typedef struct {
        int header;
        logic [7:0] payload;
        bit valid;
    } my_unpacked_struct_t;
    typedef union {
        real rval;
        longint lval;
    } my_unpacked_union_t;
    typedef struct {
        my_unpacked_struct_t item;
        my_unpacked_union_t value;
        rand int rand_member; 
    } my_nested_struct_t;
    my_unpacked_struct_t packet;
    my_unpacked_union_t data_value;
    my_nested_struct_t nested_data;
    always_comb begin
        packet.header = 1;
        packet.payload = data_in[7:0];
        packet.valid = data_in[15];
        data_value.lval = data_in; 
        nested_data.item = packet;
        nested_data.value = data_value;
        checksum_out = packet.payload + data_value.lval[7:0];
    end
endmodule
module packed_struct_module (
    input logic [31:0] packed_in,
    output logic [7:0] packed_out
);
    typedef struct packed {
        logic [3:0] field_a;
        logic [19:0] field_b;
        randc bit [7:0] field_c; 
        logic [1:0] field_d;
    } my_packed_struct_t;
    typedef union packed {
        logic [15:0] u_field_a;
        logic [7:0] u_field_b;
    } my_packed_union_t;
    my_packed_struct_t my_data;
    my_packed_union_t my_union_data;
    always_comb begin
        my_data = packed_in; 
        my_union_data.u_field_a = packed_in[15:0]; 
        packed_out = my_data.field_a + my_data.field_c + my_union_data.u_field_b;
    end
    typedef struct packed {
        logic [7:0] byte_array [3];
    } my_packed_array_struct_t;
    my_packed_array_struct_t array_data;
    always_comb begin
        array_data.byte_array[0] = packed_in[7:0];
        array_data.byte_array[1] = packed_in[15:8];
        array_data.byte_array[2] = packed_in[23:16];
        packed_out = packed_out + array_data.byte_array[0];
    end
endmodule
module func_task_module (
    input logic [7:0] val_in,
    output logic [7:0] val_out
);
    function automatic logic [7:0] add_one(logic [7:0] data);
        return data + 1;
    endfunction
    task automatic process_value(input logic [7:0] input_val, output logic [7:0] output_val);
        output_val = add_one(input_val);
        output_val = output_val * 2;
    endtask
    logic [7:0] processed;
    always_comb begin
        process_value(val_in, processed);
        val_out = processed;
    end
endmodule
(* systemc_header = "#include \"my_extra_header.h\"" *)
(* systemc_interface = "void my_sc_interface_method(int);" *)
module systemc_attr_module (
    input logic clk, 
    input logic rst,
    output logic done
);
    always_comb begin
        done = rst | clk;
    end
endmodule
