module top (
    input logic GGGin,
    output logic GGGout
);
    assign GGGout = GGGin;
endmodule

module GGG_always_comb (
    input logic GGGin,
    output logic GGGout
);
    always_comb begin
        //INJECT
        GGGout = GGGin;
    end
endmodule

module GGG_always_ff (
    input logic GGGin,
    input logic GGGclk,
    input logic GGGreset,
    output logic GGGout
);
    always_ff @(posedge GGGclk or posedge GGGreset) begin
        //INJECT
        if (GGGreset) begin
            GGGout <= 0;
        end else begin
            GGGout <= GGGin;
        end
    end
endmodule

module GGG_always_latch (
    input logic GGGin,
    input logic GGGenable,
    output logic GGGout
);
    always_latch begin
        //INJECT
        if (GGGenable) begin
            GGGout <= GGGin;
        end
    end
endmodule

module GGG_assign (
    input logic GGGin,
    output logic GGGout
);
    assign GGGout = GGGin;
    //INJECT
endmodule

module GGG_case (
    input logic [1:0] GGGin,
    output logic GGGout
);
    always_comb begin
        case (GGGin)
            2'b00: GGGout = 1'b0;
            2'b01: GGGout = 1'b1;
            2'b10: GGGout = 1'b0;
            2'b11: GGGout = 1'b1;
            default: GGGout = 1'b0;
        endcase
        //INJECT
    end
endmodule

module GGG_for_loop (
    input logic GGGin,
    output logic [3:0] GGGout
);
    integer GGGi;
    always_comb begin
        for (GGGi = 0; GGGi < 4; GGGi = GGGi + 1) begin
            GGGout[GGGi] = GGGin;
        end
        //INJECT
    end
endmodule

module GGG_if_else (
    input logic GGGin,
    output logic GGGout
);
    always_comb begin
        if (GGGin) begin
            GGGout = 1'b1;
        end else begin
            GGGout = 1'b0;
        end
        //INJECT
    end
endmodule

module GGG_task (
    input logic GGGin,
    output logic GGGout
);
    task GGGcompute;
        input logic GGGin;
        output logic GGGout;
        begin
            GGGout = GGGin;
            //INJECT
        end
    endtask

    always_comb begin
        GGGcompute(GGGin, GGGout);
    end
endmodule

module GGG_function (
    input logic GGGin,
    output logic GGGout
);
    function logic GGGfunc(logic GGGin);
        begin
            GGGfunc = GGGin;
            //INJECT
        end
    endfunction

    always_comb begin
        GGGout = GGGfunc(GGGin);
    end
endmodule

module GGG_generate (
    input logic GGGin,
    output logic [1:0] GGGout
);
    genvar GGGi;
    generate
        for (GGGi = 0; GGGi < 2; GGGi = GGGi + 1) begin
            assign GGGout[GGGi] = GGGin;
        end
    endgenerate
    //INJECT
endmodule

module GGG_struct (
    input logic GGGin,
    output logic GGGout
);
    typedef struct packed {
        logic a;
        logic b;
    } GGGstruct_t;

    GGGstruct_t GGGdata;

    always_comb begin
        GGGdata.a = GGGin;
        GGGdata.b = ~GGGin;
        GGGout = GGGdata.a & GGGdata.b;
        //INJECT
    end
endmodule
