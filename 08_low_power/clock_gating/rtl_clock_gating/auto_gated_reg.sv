// Automatic Register Clock Gating
// Registers with enable signals that benefit from clock gating

module auto_gated_reg #(
    parameter WIDTH = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             en,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);

    // ============================================
    // METHOD 1: Let synthesis tool auto-insert ICG
    // ============================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            data_out <= '0;
        else if (en)
            data_out <= data_in;
    end
    
    // Synthesis tool recognizes this pattern and inserts ICG cell
    // Enable signal becomes clock gate enable
    
    /*
     * Synthesized to:
     *   icg_cell u_icg (.clk, .en, .test_en(scan_en), .gclk);
     *   always_ff @(posedge gclk or negedge rst_n)
     *     data_out <= data_in;
     */

endmodule

// ============================================
// MANUAL CLOCK GATING
// ============================================

module manual_gated_reg #(
    parameter WIDTH = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             test_en,
    input  logic             en,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);

    // Manually instantiate ICG for explicit control
    logic gclk;
    
    icg_cell u_icg (
        .clk     (clk),
        .en      (en),
        .test_en (test_en),
        .gclk    (gclk)
    );
    
    always_ff @(posedge gclk or negedge rst_n) begin
        if (!rst_n)
            data_out <= '0;
        else
            data_out <= data_in;
    end

endmodule

// ============================================
// MULTI-BIT REGISTER BANK
// ============================================

module gated_reg_bank #(
    parameter WIDTH = 32,
    parameter DEPTH = 16
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic [DEPTH-1:0]        wr_en,
    input  logic [$clog2(DEPTH)-1:0] wr_addr,
    input  logic [WIDTH-1:0]        wr_data,
    output logic [WIDTH-1:0]        regs [DEPTH]
);

    // Each register has individual clock gating
    genvar i;
    generate
        for (i = 0; i < DEPTH; i++) begin : gen_regs
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n)
                    regs[i] <= '0;
                else if (wr_en[i])
                    regs[i] <= wr_data;
            end
            
            // Synthesis inserts ICG per register
        end
    endgenerate

endmodule

// ============================================
// CONDITIONAL ENABLE REGISTER
// ============================================

module conditional_gated_reg #(
    parameter WIDTH = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             mode,
    input  logic             en1,
    input  logic             en2,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);

    // Enable based on mode
    logic effective_en;
    assign effective_en = mode ? en1 : en2;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            data_out <= '0;
        else if (effective_en)
            data_out <= data_in;
    end
    
    // ICG uses effective_en as gate control

endmodule

// ============================================
// SHIFT REGISTER WITH CLOCK GATING
// ============================================

module gated_shift_reg #(
    parameter WIDTH = 8,
    parameter DEPTH = 4
) (
    input  logic            clk,
    input  logic            rst_n,
    input  logic            shift_en,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);

    logic [WIDTH-1:0] stages [DEPTH];
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < DEPTH; i++)
                stages[i] <= '0;
        end else if (shift_en) begin
            stages[0] <= data_in;
            for (int i = 1; i < DEPTH; i++)
                stages[i] <= stages[i-1];
        end
    end
    
    assign data_out = stages[DEPTH-1];
    
    // All stages gated together (single ICG)

endmodule

// ============================================
// CLOCK-GATED COUNTER
// ============================================

module gated_counter #(
    parameter WIDTH = 16
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             count_en,
    input  logic             clear,
    output logic [WIDTH-1:0] count
);

    logic en;
    assign en = count_en | clear;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= '0;
        else if (en) begin
            if (clear)
                count <= '0;
            else
                count <= count + 1;
        end
    end

endmodule

// ============================================
// USAGE NOTES
// ============================================

/*
 * Automatic Clock Gating (ACG):
 *
 * Synthesis tools recognize this pattern:
 *   always_ff @(posedge clk)
 *     if (enable)
 *       reg <= value;
 *
 * And transform to:
 *   ICG: gclk = clk & enable
 *   always_ff @(posedge gclk)
 *     reg <= value;
 *
 * Tool Commands (Synopsys):
 *   set_clock_gating_style \
 *     -sequential_cell latch \
 *     -positive_edge_logic {and} \
 *     -control_point before \
 *     -control_signal scan_enable
 *
 * Tool Commands (Cadence):
 *   set_attribute lp_clock_gating_style sequential
 *
 * When ACG is Applied:
 *
 * ✓ Register with enable signal
 * ✓ Enable active >50% of time (not worth gating if always on)
 * ✓ Fan-out > threshold (e.g., 6 FFs)
 * ✓ Not in critical timing path
 *
 * When ACG is NOT Applied:
 *
 * ✗ Enable toggles every cycle
 * ✗ Single flip-flop (overhead > savings)
 * ✗ Critical path (gating adds delay)
 * ✗ Already manually gated
 *
 * Power Savings Estimation:
 *
 *   P_saved = N_regs × C_reg × V² × f × (1 - α)
 *   Where:
 *     N_regs = number of registers gated
 *     C_reg = register capacitance
 *     V = supply voltage
 *     f = frequency
 *     α = activity factor (% time enabled)
 *
 * Example:
 *   32 registers, enabled 20% of time
 *   Save 80% of register clock power
 *   If registers = 5% of total power
 *   Overall savings = 4% of chip power
 *
 * Best Practices:
 *
 * 1. Use enable signals consistently
 * 2. Group related registers for shared ICG
 * 3. Don't gate critical paths
 * 4. Verify power with simulation
 * 5. Check timing after gating
 * 6. Use test_en for DFT
 *
 * Common Patterns:
 *
 * // State machine registers
 * always_ff @(posedge clk)
 *   if (state_en)
 *     state <= next_state;
 *
 * // Data path registers
 * always_ff @(posedge clk)
 *   if (data_valid)
 *     data <= new_data;
 *
 * // Config registers (rarely change)
 * always_ff @(posedge clk)
 *   if (config_wr)
 *     config_reg <= config_data;
 *
 * Verification:
 *
 * 1. Functional: Same behavior as ungated
 * 2. Timing: Meet setup/hold on enable
 * 3. Power: Measure reduction in sim
 * 4. Coverage: Test all enable patterns
 */
