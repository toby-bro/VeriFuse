module task_module (
    input  logic       clk,
    input  logic       rst_n,
    input  logic       start,
    input  logic [7:0] data_in,
    output logic       done,
    output logic [7:0] data_out
);
    // Add verilator lint directives to suppress case coverage warning
    /* verilator lint_off CASEINCOMPLETE */

    typedef enum logic [1:0] {IDLE, PROCESSING, FINISHED} state_t;
    state_t state, next_state;
    logic [7:0] temp_data;
    
    // Switching to a consistent non-blocking style for temp_data
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            temp_data <= 8'h00;
        end else begin
            state <= next_state;
            if (state == PROCESSING) begin
                // Instead of using a task with blocking assignment, 
                // directly use non-blocking assignment
                temp_data <= data_in << 1;
            end
        end
    end
    
    // Keep the task for future reference, but don't use it
    // in the always_ff block to avoid mixing assignment types
    task process_data(input logic [7:0] in_data, output logic [7:0] out_data);
        out_data = in_data << 1;  
    endtask
    
    always_comb begin
        next_state = state;
        
        case (state)
            IDLE: 
                if (start) next_state = PROCESSING;
            PROCESSING: 
                next_state = FINISHED;
            FINISHED: 
                if (!start) next_state = IDLE;
            default: // Add default case to handle all enum values
                next_state = IDLE;
        endcase
    end
    
    assign done = (state == FINISHED);
    assign data_out = temp_data;
endmodule
