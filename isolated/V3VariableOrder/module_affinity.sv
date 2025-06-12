class MyClass;
    int data;
    function new(int val);
        data = val;
    endfunction
endclass

module module_affinity (
    input logic [7:0] input_data_aff,
    input logic enable_aff,
    input logic reset_aff,
    input logic clk_aff,
    output logic [7:0] output_comb_aff,
    output logic [7:0] output_ff_aff
);
    logic [7:0] comb_var1;
    logic [7:0] comb_var2;
    logic [7:0] ff1_var1;
    logic [7:0] ff1_var2;
    logic [7:0] ff2_var1;
    logic [7:0] ff2_var2;
    int shared_var;
    logic [7:0] shared_comb_ff1;
    logic [7:0] shared_ff1_ff2;
    static int static_shared_var;
    MyClass my_class_handle1;
    MyClass my_class_handle2;
    always_comb begin
        MyClass temp_handle1, temp_handle2;
        comb_var1 = input_data_aff + (shared_comb_ff1 != 0 ? shared_comb_ff1 : 1);
        comb_var2 = input_data_aff << 1;
        shared_var = $signed(comb_var1) + $signed(comb_var2);
        if (input_data_aff[0] && enable_aff) begin
            temp_handle1 = new(shared_var + static_shared_var);
        end else begin
            temp_handle1 = null;
        end
        my_class_handle1 = temp_handle1;
        if (input_data_aff[1] && enable_aff) begin
            temp_handle2 = new(shared_ff1_ff2 + static_shared_var);
        end else begin
            temp_handle2 = null;
        end
        my_class_handle2 = temp_handle2;
        output_comb_aff = comb_var1 ^ comb_var2;
    end
    always_ff @(posedge clk_aff or posedge reset_aff) begin
        if (reset_aff) begin
            ff1_var1 <= 8'b0;
            ff1_var2 <= 8'b0;
            shared_comb_ff1 <= 8'b0;
        end else begin
            ff1_var1 <= shared_var;
            ff1_var2 <= ff1_var1 + (my_class_handle1 != null ? my_class_handle1.data : 0);
            shared_comb_ff1 <= ff1_var2;
            static_shared_var <= static_shared_var + 1;
        end
    end
    always_ff @(posedge enable_aff or posedge reset_aff) begin
        if (reset_aff) begin
            ff2_var1 <= 8'b0;
            ff2_var2 <= 8'b0;
            output_ff_aff <= 8'b0;
            shared_ff1_ff2 <= 8'b0;
        end else begin
            ff2_var1 <= shared_ff1_ff2;
            ff2_var2 <= ff2_var1 + (my_class_handle2 != null ? my_class_handle2.data : 0);
            shared_ff1_ff2 <= ff2_var2;
            output_ff_aff <= ff2_var2;
            static_shared_var <= static_shared_var + 1;
        end
    end
endmodule

