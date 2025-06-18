module module_with_unpacked_array (
    input logic [3:0] array_in_val,
    input logic [1:0] array_index,
    input logic clk,
    input logic forced_input_driver,
    output logic [3:0] array_out_val,
    output logic forced_output_monitor,
    (* verilator public *) output logic [7:0] public_output_wire
);
    logic [3:0] unpacked_reg_array [0:3];
    (* verilator public *) logic [3:0] public_unpacked_array [0:1];
    (* wire_force_assign *) logic forced_internal_in;
    (* wire_force_release *) logic forced_internal_out;
    always_ff @(posedge clk) begin
        unpacked_reg_array[array_index] <= array_in_val;
        public_unpacked_array[0] <= array_in_val;
        public_unpacked_array[1] <= array_out_val;
    end
    assign array_out_val = unpacked_reg_array[array_index];
    assign public_output_wire = public_unpacked_array[0] + public_unpacked_array[1];
    logic local_clk_ref;
    assign local_clk_ref = clk;
    assign forced_internal_in = forced_input_driver;
    assign forced_output_monitor = forced_internal_out;
endmodule

