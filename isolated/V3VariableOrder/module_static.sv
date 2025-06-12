class MyClass;
    int data;
    function new(int val);
        data = val;
    endfunction
endclass

module module_static (
    output logic [3:0] data_out_static,
    output logic static_flag,
    input logic [3:0] data_in_static,
    input logic enable_static,
    input logic reset_static,
    input logic clk_static
);
    static int static_counter;
    static logic [3:0] static_reg;
    static real static_real_val;
    static integer static_integer_val;
    logic [3:0] non_static_reg;
    logic [3:0] comb_var;
    real non_static_real_comb;
    MyClass my_static_handle;
    always_comb begin
        MyClass temp_handle;
        comb_var = static_reg + data_in_static;
        non_static_real_comb = static_real_val * 2.0;
        if (data_in_static[0] && enable_static && (static_counter > 10)) begin
            temp_handle = new(static_counter + non_static_reg[0]);
        end else begin
            temp_handle = null;
        end
        my_static_handle = temp_handle;
        data_out_static = comb_var + non_static_reg + (my_static_handle != null ? my_static_handle.data : 0);
        static_flag = (static_counter > 100);
    end
    always_ff @(posedge clk_static or posedge reset_static) begin
        if (reset_static) begin
            static_counter <= 0;
            static_reg <= 0;
            static_real_val <= 0.0;
            static_integer_val <= 0;
            non_static_reg <= 0;
        end else begin
            static_counter <= static_counter + 1;
            static_reg <= data_in_static;
            static_real_val <= $itor(static_counter) + 0.5;
            static_integer_val <= static_integer_val + 1;
            non_static_reg <= static_reg + data_in_static;
        end
    end
endmodule

