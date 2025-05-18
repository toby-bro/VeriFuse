module basic_module (
    input logic in1,
    output logic out1
);
logic internal_wire;
logic internal_reg;
assign internal_wire = in1;
always @(*) begin
    internal_reg = internal_wire;
end
assign out1 = internal_reg;
endmodule
module proc_block_module (
    input logic [7:0] in1,
    output logic [15:0] out1
);
function automatic logic [7:0] simple_func(logic [7:0] arg);
    simple_func = arg + 1;
endfunction
task automatic simple_task(input logic [7:0] arg_in, output logic [7:0] arg_out);
    arg_out = simple_func(arg_in);
endtask
task automatic task_with_local_init(input logic [7:0] arg_in, output logic [7:0] arg_out);
    logic [7:0] local_temp;
    local_temp = arg_in;
    arg_out = local_temp + 2;
endtask
import "DPI-C" task my_dpi_task(input int value, output int result);
export "DPI-C" task my_exported_task;
task my_exported_task(input int val_in, output int val_out);
    val_out = val_in * 2;
endtask
always @(*) begin
    logic [7:0] temp_var1, temp_var2;
    int dpi_in;
    int dpi_out;
    simple_task(in1, temp_var1);
    task_with_local_init(temp_var1, temp_var2);
    dpi_in = temp_var2;
    my_exported_task(dpi_in, dpi_out);
    out1 = {temp_var2, dpi_out[7:0]};
end
endmodule
module class_and_constraint_module (
    input logic clk,
    input logic reset,
    input logic in1,
    output logic out1
);
parameter int P = 10;
class SimpleClassWithConstraints;
    rand logic [3:0] rand_var;
    randc logic [3:0] randc_var;
    logic member_var;
    constraint c_randc {
        randc_var < P;
    }
    constraint c_solve_before {
        solve rand_var before randc_var;
        rand_var > 0;
    }
    constraint c_dist {
        randc_var dist { 0 := 1, 1 := 2, [2:3] := 3, 4 :/ 4 };
    }
    constraint c_soft {
        soft rand_var inside { [0:7] };
    }
    function new();
        member_var = 1'b0;
    endfunction
    function automatic void set_var(logic val);
        member_var = val;
    endfunction
    function automatic logic get_combined;
        get_combined = randc_var[0] ^ rand_var[0];
    endfunction
    function destroy();
    endfunction
endclass
SimpleClassWithConstraints my_instance;
logic out1_reg;
always @(posedge clk or posedge reset) begin
    if (reset) begin
        my_instance = null;
        out1_reg <= 1'b0;
    end else begin
        if (my_instance == null) begin
            my_instance = new();
        end
        if (my_instance != null) begin 
            logic combined_val;
            my_instance.set_var(in1);
            combined_val = my_instance.get_combined();
            out1_reg <= combined_val ^ my_instance.member_var;
        end else begin
            out1_reg <= 1'b0; 
        end
    end
end
assign out1 = out1_reg;
endmodule
module generate_module (
    input logic [3:0] in1,
    output logic [3:0] out1
);
genvar i;
logic [3:0] temp_out;
generate
    for (i = 0; i < 4; i++) begin : gen_loop
        task automatic gen_task(input logic arg_in, output logic arg_out);
             arg_out = arg_in ^ (i % 2);
        endtask
        always @(*) begin
            logic iter_out;
            gen_task(in1[i], iter_out);
            temp_out[i] = iter_out;
        end
    end
endgenerate
generate
    if (4 == 4) begin : gen_if_true
        assign out1 = temp_out;
    end else begin : gen_if_false
        assign out1 = 4'b0;
    end
endgenerate
endmodule
module file_io_module (
    input logic clk,
    input integer in1_fd,
    output integer out1
);
integer ferror_status_reg;
integer feof_status_reg;
logic [31:0] read_data_packed_reg;
integer fclose_result_reg;
integer out1_reg;
always @(posedge clk) begin
    integer temp_ferror;
    integer temp_feof;
    integer temp_fclose;
    logic [31:0] temp_read_data;
    $fread(temp_read_data, in1_fd);
    temp_ferror = $ferror(in1_fd);
    temp_feof = $feof(in1_fd);
    temp_fclose = $fclose(in1_fd);
    read_data_packed_reg <= temp_read_data;
    ferror_status_reg <= temp_ferror;
    feof_status_reg <= temp_feof;
    fclose_result_reg <= temp_fclose;
    out1_reg <= read_data_packed_reg + ferror_status_reg + feof_status_reg + fclose_result_reg;
end
assign out1 = out1_reg;
endmodule
module format_io_module (
    input logic [7:0] in1,
    input string in_str,
    output logic [7:0] out1
);
always @(*) begin
    logic [7:0] scanned_val;
    int sscanf_result;
    string complex_format_str;
    int fprintf_result;
    string formatted_str_local;
    sscanf_result = $sscanf(in_str, "Value: %d (hex: %h) from str: %s", scanned_val, scanned_val, in_str);
    complex_format_str = $sformatf("Module: %m, Lib: %l - Val: %d (hex: %h), String: %s", scanned_val, scanned_val, in_str);
    formatted_str_local = complex_format_str;
    fprintf_result = $fprintf(0, "Formatted: %s\n", formatted_str_local);
    out1 = scanned_val + sscanf_result + in1 + fprintf_result;
end
endmodule
module assertion_module (
    input logic clk,
    input logic reset,
    input logic data_in,
    output logic out1
);
logic prev_data;
always @(posedge clk or posedge reset) begin
    if (reset) begin
        prev_data <= 1'b0;
    end else begin
        prev_data <= data_in;
    end
end
assert property (@(posedge clk) disable iff (reset) data_in |-> prev_data);
assign out1 = prev_data;
endmodule
(* verilator public_module *)
(* verilator hier_block *)
module pragma_module (
    input logic in1,
    output logic out1
);
(* verilator public_task *)
task automatic pragma_task(input logic arg_in, output logic arg_out);
    (* verilator coverage_block_off *)
    arg_out = arg_in;
endtask
(* verilator public *)
logic temp_out;
always @(*) begin
    pragma_task(in1, temp_out);
    out1 = temp_out;
end
endmodule
module case_module (
    input logic [1:0] in1_selector,
    input logic [3:0] in2_data,
    output logic [3:0] out1
);
always @(*) begin
    case (in1_selector)
        2'b00: out1 = in2_data + 1;
        2'b01: out1 = in2_data - 1;
        default: out1 = 4'b0;
    endcase
end
endmodule
module let_module (
    input logic [7:0] in1,
    output logic [7:0] out1
);
let ADD_ONE(x) = x + 1;
logic [7:0] temp_var;
always @(*) begin
    temp_var = ADD_ONE(in1);
    out1 = temp_var;
end
endmodule
interface simple_if (input logic clk);
    logic data;
    modport mp (input data);
endinterface
module interface_module (
    input logic clk,
    simple_if.mp iface_port,
    output logic out1
);
logic internal_data;
always @(posedge clk) begin
    internal_data <= iface_port.data;
end
assign out1 = internal_data;
endmodule
primitive basic_udp (q, a, b);
    output q;
    input a, b;
    table
      0 0 : 0;
      0 1 : 1;
      1 0 : 1;
      1 1 : 0;
      ? x : ?;
      x ? : ?;
    endtable
endprimitive
module udp_module (
    input logic in_a,
    input logic in_b,
    output logic out_q
);
    basic_udp u_basic_udp (out_q, in_a, in_b);
endmodule
