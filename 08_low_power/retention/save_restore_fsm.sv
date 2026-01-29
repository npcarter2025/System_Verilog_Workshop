// Save/Restore FSM for Power Management
// Controls the sequence of saving and restoring state

module save_restore_fsm (
    input  logic clk,
    input  logic rst_n,
    input  logic power_down_req,
    input  logic power_up_done,
    output logic save,
    output logic restore,
    output logic iso_en,
    output logic power_switch_en,
    output logic [2:0] state
);

    typedef enum logic [2:0] {
        ACTIVE      = 3'b000,
        SAVING      = 3'b001,
        ISOLATING   = 3'b010,
        POWERED_OFF = 3'b011,
        POWERING_ON = 3'b100,
        RESTORING   = 3'b101
    } state_t;
    
    state_t current_state, next_state;
    logic [7:0] counter;
    
    // State register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            current_state <= ACTIVE;
        else
            current_state <= next_state;
    end
    
    // Counter for timing
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            counter <= 0;
        else if (current_state != next_state)
            counter <= 0;
        else
            counter <= counter + 1;
    end
    
    // Next state logic
    always_comb begin
        next_state = current_state;
        
        case (current_state)
            ACTIVE: begin
                if (power_down_req)
                    next_state = SAVING;
            end
            
            SAVING: begin
                if (counter >= 8'd10)
                    next_state = ISOLATING;
            end
            
            ISOLATING: begin
                if (counter >= 8'd5)
                    next_state = POWERED_OFF;
            end
            
            POWERED_OFF: begin
                if (power_up_done)
                    next_state = POWERING_ON;
            end
            
            POWERING_ON: begin
                if (counter >= 8'd10)
                    next_state = RESTORING;
            end
            
            RESTORING: begin
                if (counter >= 8'd10)
                    next_state = ACTIVE;
            end
        endcase
    end
    
    // Output logic
    always_comb begin
        save = (current_state == SAVING);
        restore = (current_state == RESTORING);
        iso_en = (current_state == ISOLATING || 
                  current_state == POWERED_OFF);
        power_switch_en = (current_state != POWERED_OFF);
    end
    
    assign state = current_state;

endmodule
