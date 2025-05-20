module case_pragmas_mod (
    input logic [3:0] case_inside_val,
    input logic [3:0] range_start,
    input logic [3:0] range_end,
    output logic case_pragma_out,
    input logic [1:0] case_expr
);
    logic [4:0] internal_out = 0;
      always @* begin
    internal_out = 0;
    (* full, parallel *)
    case (case_expr)
      2'b00: internal_out = 1;
      2'b01: internal_out = 2;
      2'b10: internal_out = 3;
      default: internal_out = 4;
    endcase
    (* unique, priority *)
    casez (case_expr)
      2'b1?: internal_out = 5;
      2'b0?: internal_out = 6;
      default: internal_out = 7;
    endcase
    (* unique0 *)
    casez (case_expr)
      2'b1?: internal_out = 8;
      2'b0?: internal_out = 9;
    endcase
    (* full *)
    case (case_expr)
      2'b00: internal_out = 10;
      2'b01: internal_out = 11;
      2'b10: internal_out = 12;
      default: internal_out = 13;
    endcase
    (* parallel *)
    case (case_inside_val)
      4'd0, 4'd1: internal_out = 14;
      4'd2, 4'd3: internal_out = 15;
      default: internal_out = 18;
    endcase
    (* unique *)
    case (case_inside_val)
      case_inside_val inside {[range_start:range_end]}: internal_out = 16;
      case_inside_val inside {8}: internal_out = 17;
      default: internal_out = 18;
    endcase
    (* unique0 *)
    case (case_inside_val)
       case_inside_val inside {4'd10, 4'd11}: internal_out = 19;
       case_inside_val inside {4'd12}: internal_out = 20;
    endcase
      end
      assign case_pragma_out = internal_out;
endmodule

