// Power State Monitor
// Checks for legal power state transitions

module power_state_monitor (
    input logic clk,
    input logic rst_n,
    input logic power_en,
    input logic iso_en,
    input logic save,
    input logic restore
);

    typedef enum logic [2:0] {
        ACTIVE      = 3'b000,
        SAVING      = 3'b001,
        ISOLATED    = 3'b010,
        POWERED_OFF = 3'b011,
        POWERING_ON = 3'b100,
        RESTORING   = 3'b101
    } power_state_t;
    
    power_state_t state, prev_state;
    
    // Track state
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= ACTIVE;
        else begin
            prev_state <= state;
            
            // Determine current state from signals
            if (power_en && !iso_en && !save && !restore)
                state <= ACTIVE;
            else if (save)
                state <= SAVING;
            else if (iso_en && !power_en)
                state <= POWERED_OFF;
            else if (restore)
                state <= RESTORING;
        end
    end
    
    // Assertion: Legal state transitions
    property legal_transition;
        @(posedge clk) disable iff (!rst_n)
        (prev_state == ACTIVE && state != ACTIVE) |-> (state == SAVING) ||
        (prev_state == SAVING) |-> (state == ISOLATED) ||
        (prev_state == ISOLATED) |-> (state == POWERED_OFF) ||
        (prev_state == POWERED_OFF && state != POWERED_OFF) |-> (state == POWERING_ON) ||
        (prev_state == POWERING_ON) |-> (state == RESTORING) ||
        (prev_state == RESTORING) |-> (state == ACTIVE);
    endproperty
    
    a_legal_trans: assert property (legal_transition)
        else $error("Illegal power state transition: %s -> %s", 
                   prev_state.name(), state.name());
    
    // Assertion: Isolation active when powered off
    property iso_when_off;
        @(posedge clk) disable iff (!rst_n)
        !power_en |-> iso_en;
    endproperty
    
    a_iso_off: assert property (iso_when_off)
        else $error("Isolation not active when powered off");
    
    // Assertion: Save before power-down
    property save_before_powerdown;
        @(posedge clk) disable iff (!rst_n)
        $fell(power_en) |-> $past(save, 1);
    endproperty
    
    a_save_first: assert property (save_before_powerdown)
        else $error("Power-down without save");
    
    // Assertion: Restore after power-up
    property restore_after_powerup;
        @(posedge clk) disable iff (!rst_n)
        $rose(power_en) |-> ##[1:10] restore;
    endproperty
    
    a_restore_after: assert property (restore_after_powerup)
        else $error("No restore after power-up");
    
    // Monitor state changes
    always @(state) begin
        if (state != prev_state)
            $display("@%0t: Power state: %s -> %s", 
                    $time, prev_state.name(), state.name());
    end

endmodule
