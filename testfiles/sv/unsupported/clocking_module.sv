module clocking_module (
    input  logic       clk,
    input  logic       rst_n,
    input  logic [7:0] data_in,
    input  logic       valid_in,
    input  logic       ready_in,
    output logic [7:0] data_out,
    output logic       valid_out,
    output logic       ready_out
);

    // Internal registers
    logic [7:0] buffer_reg;
    logic [7:0] processed_data;
    logic       processing_valid;
    
    // Clocking block with proper input/output skew control
    clocking driver_cb @(posedge clk);
        default input #1step output #0;  // Setup/hold timing
        input  negedge rst_n;
        input  data_in, valid_in, ready_in;
        output data_out, valid_out, ready_out;
    endclocking
    
    // Clocking block for sampling (useful for testbenches)
    clocking monitor_cb @(posedge clk);
        default input #0 output #1step;
        input data_out, valid_out, ready_out;
        input data_in, valid_in, ready_in;
    endclocking
    
    // Modport for interface usage
    modport driver_mp (clocking driver_cb, input rst_n);
    modport monitor_mp (clocking monitor_cb, input rst_n);
    
    // Main processing pipeline with handshaking
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_out <= 8'h00;
            valid_out <= 1'b0;
            ready_out <= 1'b1;
            buffer_reg <= 8'h00;
            processing_valid <= 1'b0;
        end else begin
            // Input stage - accept data when valid and we're ready
            if (valid_in && ready_out) begin
                buffer_reg <= data_in;
                processing_valid <= 1'b1;
                ready_out <= 1'b0;  // Not ready for next data yet
            end
            
            // Processing stage - simple data transformation
            if (processing_valid) begin
                // More realistic processing: bit rotation + XOR
                processed_data <= {buffer_reg[6:0], buffer_reg[7]} ^ 8'hA5;
                
                // Output stage - present data when downstream is ready
                if (ready_in) begin
                    data_out <= processed_data;
                    valid_out <= 1'b1;
                    processing_valid <= 1'b0;
                    ready_out <= 1'b1;  // Ready for next input
                end
            end else begin
                // Clear valid when data is accepted
                if (valid_out && ready_in) begin
                    valid_out <= 1'b0;
                end
            end
        end
    end
    
    // Assertions for protocol checking (typical in real designs)
    `ifdef ASSERTIONS_ON
    property valid_stable;
        @(posedge clk) disable iff (!rst_n)
        valid_out && !ready_in |=> $stable(data_out);
    endproperty
    
    property ready_valid_handshake;
        @(posedge clk) disable iff (!rst_n)
        valid_out |-> ##[0:$] ready_in;
    endproperty
    
    assert property (valid_stable) else $error("Data not stable during valid");
    assert property (ready_valid_handshake) else $error("Handshake protocol violation");
    `endif

endmodule