module task_module (
    input  logic       clk,
    input  logic       rst_n,
    input  logic       start,
    input  logic [7:0] data_in,
    output logic       done,
    output logic [7:0] data_out
);
    // Internal state
    typedef enum logic [1:0] {IDLE, PROCESSING, FINISHED} state_t;
    state_t state, next_state;
    logic [7:0] temp_data;
    
    // Sequential logic for state
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            temp_data <= 8'h00;
        end else begin
            state <= next_state;
            if (state == PROCESSING) begin
                process_data(data_in, temp_data);
            end
        end
    end
    
    // Task definition
    task process_data(input logic [7:0] in_data, output logic [7:0] out_data);
        out_data = in_data << 1;  // Simple left shift
    endtask
    
    // Next state logic
    always_comb begin
        next_state = state;
        
        case (state)
            IDLE: 
                if (start) next_state = PROCESSING;
            PROCESSING: 
                next_state = FINISHED;
            FINISHED: 
                if (!start) next_state = IDLE;
        endcase
    end
    
    // Output logic
    assign done = (state == FINISHED);
    assign data_out = temp_data;
endmodule
