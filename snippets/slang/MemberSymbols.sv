module mod_empty (
    input  logic in1,
    output logic out1
);
    logic temp_empty;
    assign temp_empty = in1;
    assign out1 = temp_empty;
    class my_class_empty;
        int val;
        function new(int v);
            val = v;
        endfunction
    endclass
    always_comb begin
        my_class_empty cls;
        cls = new(1);
    end
endmodule
package dummy_pkg;
    parameter int PKG_PARAM_EXP  = 8;
    parameter int PKG_PARAM_WILD = 16;
    logic pkg_var_exp;
    logic pkg_var_wild;
    function int pkg_func_exp(int a);
        return a + 1;
    endfunction
endpackage
module mod_imports (
    input  logic in_imp,
    output logic out_imp
);
    import dummy_pkg::PKG_PARAM_EXP;
    import dummy_pkg::*;
    logic [PKG_PARAM_EXP-1:0]  data_exp;
    logic [PKG_PARAM_WILD-1:0] data_wild;
    int   func_result;
    always_comb begin
        data_exp    = PKG_PARAM_EXP;
        data_wild   = PKG_PARAM_WILD;
        func_result = pkg_func_exp(in_imp);
        out_imp     = data_exp[0] ^ data_wild[0] ^ func_result[0];
    end
    class my_class_imp;
        int val;
        function new(int v);
            val = v;
        endfunction
    endclass
    always_comb begin
        my_class_imp cls;
        cls = new(PKG_PARAM_EXP);
    end
endmodule
module mod_assign (
    input  wire        in_val_simple,
    input  wire [7:0]  data_in_assign,
    input  wire        in_drive,
    input  wire        var_in_assign,
    output wire        simple_out_assign,
    output wire [7:0]  data_out_assign,
    output wire        drive_out_assign,
    output wire        var_out_assign
);
    wire internal_simple;
    assign internal_simple     = in_val_simple;
    assign simple_out_assign   = internal_simple;
    assign (weak1, weak0) drive_out_assign = in_drive;
    assign (supply0, supply1) data_out_assign = data_in_assign;
    assign var_out_assign = var_in_assign;
    class my_class_assign;
        int count;
        function new();
            count = 0;
        endfunction
    endclass
    always_comb begin
        my_class_assign cls;
        cls = new();
        cls.count = cls.count + 1;
    end
endmodule
module mod_genvar (
    input  logic       clk,
    input  logic       input_val_gen,
    output logic [7:0] out_sum_gen
);
    genvar i;
    logic [7:0] temp_sum_gen = '0;
    generate
        for (i = 0; i < 8; i = i + 1) begin : gen_block
            always_ff @(posedge clk) begin
                if (input_val_gen)
                    temp_sum_gen[i] <= temp_sum_gen[i] + 1'b1;
            end
        end
    endgenerate
    assign out_sum_gen = temp_sum_gen;
    class my_class_genvar;
        int index;
        function new(int i_);
            index = i_;
        endfunction
    endclass
    generate
        for (i = 0; i < 8; i = i + 1) begin : gen_class_inst
            always_comb begin
                my_class_genvar cls;
                cls = new(i);
            end
        end
    endgenerate
endmodule
module mod_elab_tasks (
    input  logic dummy_in_elab,
    output logic out_status_elab
);
    parameter int VAL_ELAB = 7;
    logic unused;
    assign unused          = VAL_ELAB > 0;
    assign out_status_elab = dummy_in_elab;
    class my_class_elab;
        string status;
        function new(string s);
            status = s;
        endfunction
    endclass
    always_comb begin
        my_class_elab cls;
        cls = new("Elab task module");
    end
endmodule
primitive udp_comb (out, a, b);
    output out;
    input  a, b;
    table
        0 0 : 0;
        0 1 : 0;
        1 0 : 0;
        1 1 : 1;
        0 x : 0;
        x 0 : 0;
        1 x : 1;
        x 1 : 1;
        x x : x;
    endtable
endprimitive
primitive udp_seq (q, d, clk);
    output reg q;
    input  d, clk;
    table
        0 (01) : ? : 0;
        1 (01) : ? : 1;
        ? ?    : 0 : 0;
        ? ?    : 1 : 1;
    endtable
endprimitive
module mod_udps (
    input  wire i_a_udp,
    input  wire i_b_udp,
    input  wire i_in_seq_udp,
    input  wire i_clk_seq_udp,
    output wire o_comb_udp,
    output wire o_seq_udp
);
    wire w_comb_out;
    wire w_seq_out;
    udp_comb comb_inst (w_comb_out, i_a_udp, i_b_udp);
    udp_seq  seq_inst  (w_seq_out,  i_in_seq_udp, i_clk_seq_udp);
    assign o_comb_udp = w_comb_out;
    assign o_seq_udp  = w_seq_out;
    class my_class_udp;
        int val;
        function new(int v);
            val = v;
        endfunction
    endclass
    always_comb begin
        my_class_udp cls;
        cls = new(5);
    end
endmodule
