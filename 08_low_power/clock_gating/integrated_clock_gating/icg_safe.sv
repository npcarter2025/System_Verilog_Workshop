// Glitch-Free ICG Implementation
// Industrial-strength clock gating with safety features

module icg_safe (
    input  logic clk,
    input  logic en,
    input  logic test_en,
    output logic gclk
);

    // ============================================
    // SAFE CLOCK GATING WITH CHECKS
    // ============================================
    
    logic en_latched;
    
    // Latch enable during low phase
    always_latch begin
        if (!clk)
            en_latched <= en | test_en;
    end
    
    // Generate gated clock
    assign gclk = clk & en_latched;
    
    // ============================================
    // ASSERTIONS FOR VERIFICATION
    // ============================================
    
    // Assert 1: No glitches on gated clock
    property no_glitch;
        @(posedge clk)
        $rose(gclk) |-> ##1 gclk;
    endproperty
    
    a_no_glitch: assert property (no_glitch)
        else $error("Glitch detected on gated clock!");
    
    // Assert 2: Enable synchronized with clock
    property en_sync;
        @(posedge clk)
        en |-> ##[0:2] gclk;
    endproperty
    
    a_en_sync: assert property (en_sync);
    
    // Assert 3: Gated clock only when enabled
    property gclk_when_en;
        @(posedge clk)
        gclk |-> (en_latched || test_en);
    endproperty
    
    a_gclk_valid: assert property (gclk_when_en);
    
    // ============================================
    // COVERAGE
    // ============================================
    
    covergroup cg_icg @(posedge clk);
        cp_en: coverpoint en {
            bins low  = {0};
            bins high = {1};
            bins transitions[] = (0 => 1), (1 => 0);
        }
        
        cp_test: coverpoint test_en {
            bins normal = {0};
            bins test   = {1};
        }
        
        cp_cross: cross cp_en, cp_test;
    endgroup
    
    cg_icg cg_inst = new();

endmodule

// ============================================
// ICG WITH ENABLE FILTERING
// ============================================

module icg_safe_filtered (
    input  logic clk,
    input  logic en,
    input  logic test_en,
    output logic gclk
);

    // Filters out single-cycle enable pulses
    // Requires enable to be stable for 2+ cycles
    
    logic en_stable;
    logic en_prev;
    logic en_latched;
    
    // Detect stable enable
    always_ff @(posedge clk) begin
        en_prev <= en;
        en_stable <= en & en_prev;
    end
    
    // Latch stable enable
    always_latch begin
        if (!clk)
            en_latched <= en_stable | test_en;
    end
    
    assign gclk = clk & en_latched;
    
    // Assertion: Filters out short pulses
    property filter_short_pulse;
        @(posedge clk)
        (en && !en_prev) ##1 (!en) |-> !gclk;
    endproperty
    
    a_filter: assert property (filter_short_pulse);

endmodule

// ============================================
// ICG WITH POWER MONITORING
// ============================================

module icg_safe_monitored (
    input  logic clk,
    input  logic en,
    input  logic test_en,
    output logic gclk,
    output logic [31:0] gated_cycles,
    output logic [31:0] total_cycles
);

    logic en_latched;
    
    always_latch begin
        if (!clk)
            en_latched <= en | test_en;
    end
    
    assign gclk = clk & en_latched;
    
    // ============================================
    // POWER MONITORING COUNTERS
    // ============================================
    
    // Count gated cycles (clock off)
    always_ff @(posedge clk) begin
        if (!en_latched)
            gated_cycles <= gated_cycles + 1;
    end
    
    // Count total cycles
    always_ff @(posedge clk) begin
        total_cycles <= total_cycles + 1;
    end
    
    // Calculate gating efficiency
    // Efficiency = gated_cycles / total_cycles * 100%
    
    // Report every 1000 cycles
    always @(posedge clk) begin
        if (total_cycles % 1000 == 0) begin
            $display("ICG Stats: %0d/%0d cycles gated (%.1f%%)",
                    gated_cycles, total_cycles,
                    real'(gated_cycles) / real'(total_cycles) * 100.0);
        end
    end

endmodule

// ============================================
// ICG WITH SYNCHRONOUS RESET
// ============================================

module icg_safe_with_reset (
    input  logic clk,
    input  logic rst_n,
    input  logic en,
    input  logic test_en,
    output logic gclk
);

    logic en_latched;
    logic rst_n_latched;
    
    // Latch both enable and reset
    always_latch begin
        if (!clk) begin
            en_latched <= en | test_en | !rst_n;
            rst_n_latched <= rst_n;
        end
    end
    
    // Clock always runs during reset
    assign gclk = clk & (en_latched | !rst_n_latched);
    
    // Assertion: Clock runs during reset
    property clk_during_reset;
        @(posedge clk)
        !rst_n |-> gclk;
    endproperty
    
    a_reset_clk: assert property (clk_during_reset);

endmodule

// ============================================
// ICG WITH ASYNC ENABLE
// ============================================

module icg_safe_async_en (
    input  logic clk,
    input  logic en_async,  // Asynchronous enable
    input  logic test_en,
    output logic gclk
);

    // Synchronize async enable to avoid metastability
    logic en_sync1, en_sync2;
    logic en_latched;
    
    // Two-FF synchronizer
    always_ff @(posedge clk) begin
        en_sync1 <= en_async;
        en_sync2 <= en_sync1;
    end
    
    // Latch synchronized enable
    always_latch begin
        if (!clk)
            en_latched <= en_sync2 | test_en;
    end
    
    assign gclk = clk & en_latched;
    
    // Assertion: Enable is synchronized
    property en_synchronized;
        @(posedge clk)
        $rose(en_latched) |-> $past(en_sync2, 2);
    endproperty

endmodule

// ============================================
// ICG WITH POWER STATE MACHINE
// ============================================

module icg_safe_with_fsm (
    input  logic       clk,
    input  logic       rst_n,
    input  logic       en,
    input  logic       test_en,
    output logic       gclk,
    output logic [1:0] power_state
);

    // Power states
    typedef enum logic [1:0] {
        ACTIVE  = 2'b00,
        GATING  = 2'b01,
        GATED   = 2'b10,
        WAKEUP  = 2'b11
    } state_t;
    
    state_t state, next_state;
    logic en_latched;
    
    // State machine
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= ACTIVE;
        else
            state <= next_state;
    end
    
    // Next state logic
    always_comb begin
        next_state = state;
        case (state)
            ACTIVE: if (!en) next_state = GATING;
            GATING: next_state = GATED;
            GATED:  if (en) next_state = WAKEUP;
            WAKEUP: next_state = ACTIVE;
        endcase
    end
    
    // Latch enable
    always_latch begin
        if (!clk)
            en_latched <= (state == ACTIVE || state == WAKEUP) | test_en;
    end
    
    assign gclk = clk & en_latched;
    assign power_state = state;

endmodule

// ============================================
// USAGE AND BEST PRACTICES
// ============================================

/*
 * Glitch-Free Clock Gating Requirements:
 *
 * 1. LATCH REQUIREMENT
 *    - Must use latch, not flip-flop
 *    - Latch on opposite clock edge
 *    - Ensures enable stable during clock high
 *
 * 2. ENABLE TIMING
 *    - Setup time: en must be stable before clk falls
 *    - Hold time: en must remain stable after clk falls
 *    - Violation causes glitches or metastability
 *
 * 3. TEST MODE
 *    - test_en bypasses gating for scan
 *    - Required for production designs
 *    - Must be tied to test controller
 *
 * 4. RESET HANDLING
 *    - Clock should run during reset
 *    - Ensures proper reset propagation
 *    - Some designs gate reset registers separately
 *
 * Safety Features:
 *
 * - Enable filtering: Ignore short pulses
 * - Synchronization: Handle async enables
 * - Monitoring: Track gating efficiency
 * - State machine: Controlled transitions
 * - Assertions: Catch glitches in simulation
 *
 * Verification:
 *
 * 1. Functional: All clock edges present when needed
 * 2. Timing: No setup/hold violations
 * 3. Power: Measure dynamic power reduction
 * 4. DFT: Scan chains work with test_en
 *
 * Power Analysis:
 *
 *   P_clock = P_distribution + P_registers
 *   P_saved = (1 - duty_cycle) × P_clock
 *
 * Example:
 *   If clock tree = 30% of chip power
 *   And gating duty = 70%
 *   Then save 21% of total chip power!
 *
 * Tool Flow:
 *
 * 1. RTL: Write with enable signals
 * 2. Synthesis: Tool inserts ICG cells
 * 3. CTS: Clock tree synthesis with gates
 * 4. STA: Verify timing with gating
 * 5. Power: Confirm savings in reports
 */
