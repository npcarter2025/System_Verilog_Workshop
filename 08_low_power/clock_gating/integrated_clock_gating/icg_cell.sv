// Integrated Clock Gating (ICG) Cell
// Latch-based clock gate for power reduction
// Prevents glitches by using latch to hold enable signal

module icg_cell (
    input  logic clk,       // Input clock
    input  logic en,        // Enable signal (clock enabled when high)
    input  logic test_en,   // Test mode bypass (for DFT)
    output logic gclk       // Gated clock output
);

    // ============================================
    // LATCH-BASED CLOCK GATE
    // ============================================
    
    // The enable signal is latched during the low phase of the clock
    // This ensures enable is stable during the entire high phase,
    // preventing glitches on the gated clock
    
    logic en_latched;
    
    // Latch enable when clock is low
    always_latch begin
        if (!clk)
            en_latched <= en | test_en;  // test_en bypasses gating for scan
    end
    
    // AND gate combines clock with latched enable
    assign gclk = clk & en_latched;
    
    // ============================================
    // TIMING DIAGRAM
    // ============================================
    
    /*
     *           ___     ___     ___     ___     ___     ___
     * clk   ___|   |___|   |___|   |___|   |___|   |___|   |___
     *
     * en    ____________|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|____________
     *
     *           ___     ___     ___     ___
     * gclk  ___|   |___|   |___|   |___|   |_______________
     *
     * en_latched: Captured when clk=0, stable when clk=1
     *
     * Key Points:
     * 1. en can change during high phase of clk - no glitch
     * 2. en_latched stable during high phase - safe gating
     * 3. gclk has clean edges, no glitches
     */

endmodule

// ============================================
// POSITIVE EDGE-TRIGGERED ICG (Alternative)
// ============================================

module icg_cell_posedge (
    input  logic clk,
    input  logic en,
    input  logic test_en,
    output logic gclk
);

    logic en_latched;
    
    // For positive edge-triggered logic,
    // latch enable during high phase
    always_latch begin
        if (clk)
            en_latched <= en | test_en;
    end
    
    // Gate clock during low phase
    assign gclk = clk | ~en_latched;

endmodule

// ============================================
// PARAMETERIZED ICG CELL
// ============================================

module icg_cell_param #(
    parameter EDGE_TYPE = "NEGEDGE"  // "NEGEDGE" or "POSEDGE"
) (
    input  logic clk,
    input  logic en,
    input  logic test_en,
    output logic gclk
);

    logic en_latched;
    
    generate
        if (EDGE_TYPE == "NEGEDGE") begin : gen_negedge
            // Standard ICG for negative edge-triggered latch
            always_latch begin
                if (!clk)
                    en_latched <= en | test_en;
            end
            assign gclk = clk & en_latched;
            
        end else begin : gen_posedge
            // ICG for positive edge-triggered latch
            always_latch begin
                if (clk)
                    en_latched <= en | test_en;
            end
            assign gclk = clk | ~en_latched;
        end
    endgenerate

endmodule

// ============================================
// ICG WITH ENABLE PULSE EXTENSION
// ============================================

module icg_cell_extended (
    input  logic clk,
    input  logic en,
    input  logic test_en,
    output logic gclk
);

    // Extends enable pulse to ensure at least one clock cycle
    // Useful for single-cycle enable pulses
    
    logic en_extended;
    logic en_latched;
    
    always_ff @(posedge clk) begin
        en_extended <= en | en_extended;
    end
    
    always_latch begin
        if (!clk)
            en_latched <= en_extended | test_en;
    end
    
    assign gclk = clk & en_latched;

endmodule

// ============================================
// USAGE NOTES
// ============================================

/*
 * Clock Gating Benefits:
 * - Reduces dynamic power by 20-70%
 * - No impact on functionality when done correctly
 * - Can be automated by synthesis tools
 *
 * When to Use:
 * - Registers with enable signals
 * - Idle functional blocks
 * - Pipeline stages that can be stalled
 * - Memories not being accessed
 *
 * Design Considerations:
 * 1. Latch is required to prevent glitches
 * 2. test_en allows scan testing (DFT)
 * 3. Setup/hold timing must be met on en signal
 * 4. Clock tree must be balanced after gating
 *
 * Power Calculation:
 *   P_dynamic = α × C_load × V_dd² × f_clk
 *   Where α = activity factor (reduced by gating)
 *
 * Example Savings:
 *   If en=1 for 30% of time, save ~70% clock power
 *
 * Integration:
 *   // Before:
 *   always_ff @(posedge clk)
 *     if (en)
 *       data_reg <= data_in;
 *
 *   // After:
 *   icg_cell u_icg (.clk, .en, .test_en, .gclk);
 *   always_ff @(posedge gclk)
 *     data_reg <= data_in;
 *
 * Synthesis:
 *   - Most synthesis tools auto-insert ICG
 *   - Use set_clock_gating_style command
 *   - Verify with power reports
 *
 * Common Mistakes:
 *   ✗ Using AND gate without latch (glitches!)
 *   ✗ Forgetting test_en (breaks scan)
 *   ✗ Gating derived clocks (timing issues)
 *   ✗ Not considering clock tree
 */
