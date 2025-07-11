module mod_comb_logic (
    input logic a,
    input logic b,
    output logic y
);
    always_comb begin
        y = a & b;
    end
endmodule
module mod_seq_reg (
    input logic clk,
    input logic d,
    output logic q
);
    always_ff @(posedge clk) begin
        q <= d;
    end
endmodule
module mod_fork_join (
    input logic en,
    input int x,
    output int y1,
    output int y2
);
    always_comb begin
        y1 = 0;
        y2 = 0;
        if (en) begin
            fork : fork_block_name
                y1 = x;
                y2 = x + 1;
            join_none
        end
    end
endmodule
module mod_automatic_task (
    input int i_val,
    output int o_val
);
    task automatic update_val(input int in_v, output int out_v);
        out_v = in_v * 2;
    endtask
    always_comb begin
        int temp_val;
        update_val(i_val, temp_val);
        o_val = temp_val;
    end
endmodule
module mod_named_begin (
    input int data_in,
    output int data_out
);
    always_comb begin : my_named_block
        data_out = data_in;
    end
endmodule
class SimpleClass;
    int m_val = 10;
    function int get_val();
        return m_val;
    endfunction
endclass
module mod_class_inst (
    input logic dummy_in,
    output int data_out_class
);
    always_comb begin
        SimpleClass inst = new();
        data_out_class = inst.get_val();
    end
endmodule
module mod_logical_not (
    input logic cond_in,
    output logic cond_out
);
    always_comb begin
        cond_out = !cond_in;
    end
endmodule
