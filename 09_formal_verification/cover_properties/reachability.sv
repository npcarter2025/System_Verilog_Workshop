// Cover Properties for Reachability Analysis
// Proves that states and conditions are actually reachable
// Critical for avoiding vacuous assertion passes!

module reachability_cover_properties (
    input logic       clk,
    input logic       rst_n,
    input logic [2:0] state,
    input logic [7:0] counter,
    input logic       error_flag,
    input logic       busy,
    input logic       done
);

    // ============================================
    // STATE MACHINE REACHABILITY
    // ============================================
    
    // Define states
    localparam IDLE   = 3'b000;
    localparam WAIT   = 3'b001;
    localparam ACTIVE = 3'b010;
    localparam PROC   = 3'b011;
    localparam DONE   = 3'b100;
    localparam ERROR  = 3'b101;
    
    // Cover: Reach each state
    c_idle:   cover property (@(posedge clk) state == IDLE);
    c_wait:   cover property (@(posedge clk) state == WAIT);
    c_active: cover property (@(posedge clk) state == ACTIVE);
    c_proc:   cover property (@(posedge clk) state == PROC);
    c_done:   cover property (@(posedge clk) state == DONE);
    c_error:  cover property (@(posedge clk) state == ERROR);
    
    // ============================================
    // STATE TRANSITIONS REACHABILITY
    // ============================================
    
    // Cover: All valid transitions
    c_idle_to_wait: cover property (
        @(posedge clk) (state == IDLE) ##1 (state == WAIT)
    );
    
    c_wait_to_active: cover property (
        @(posedge clk) (state == WAIT) ##1 (state == ACTIVE)
    );
    
    c_active_to_proc: cover property (
        @(posedge clk) (state == ACTIVE) ##1 (state == PROC)
    );
    
    c_proc_to_done: cover property (
        @(posedge clk) (state == PROC) ##1 (state == DONE)
    );
    
    c_done_to_idle: cover property (
        @(posedge clk) (state == DONE) ##1 (state == IDLE)
    );
    
    // Cover: Error transitions
    c_any_to_error: cover property (
        @(posedge clk) (state != ERROR) ##1 (state == ERROR)
    );
    
    c_error_to_idle: cover property (
        @(posedge clk) (state == ERROR) ##1 (state == IDLE)
    );
    
    // ============================================
    // STATE SEQUENCES REACHABILITY
    // ============================================
    
    // Cover: Complete happy path
    sequence happy_path;
        (state == IDLE) ##1 
        (state == WAIT) ##1 
        (state == ACTIVE) ##1 
        (state == PROC) ##1 
        (state == DONE);
    endsequence
    
    c_happy_path: cover property (@(posedge clk) happy_path);
    
    // Cover: Fast path (skip WAIT)
    sequence fast_path;
        (state == IDLE) ##1 (state == ACTIVE);
    endsequence
    
    c_fast_path: cover property (@(posedge clk) fast_path);
    
    // Cover: Loop back from ACTIVE to WAIT
    sequence loop_path;
        (state == ACTIVE) ##1 (state == WAIT);
    endsequence
    
    c_loop: cover property (@(posedge clk) loop_path);
    
    // Cover: Error recovery
    sequence error_recovery;
        (state == ERROR) ##[1:10] (state == DONE);
    endsequence
    
    c_error_recover: cover property (@(posedge clk) error_recovery);
    
    // ============================================
    // BOUNDARY VALUE REACHABILITY
    // ============================================
    
    // Cover: Counter boundaries
    c_counter_zero: cover property (@(posedge clk) counter == 0);
    c_counter_max:  cover property (@(posedge clk) counter == 255);
    c_counter_half: cover property (@(posedge clk) counter == 128);
    
    // Cover: Counter overflow
    c_counter_overflow: cover property (
        @(posedge clk) (counter == 255) ##1 (counter == 0)
    );
    
    // ============================================
    // FLAG COMBINATIONS REACHABILITY
    // ============================================
    
    // Cover: Various flag combinations
    c_busy_not_done: cover property (
        @(posedge clk) busy && !done
    );
    
    c_done_not_busy: cover property (
        @(posedge clk) done && !busy
    );
    
    c_all_flags_clear: cover property (
        @(posedge clk) !busy && !done && !error_flag
    );
    
    c_error_set: cover property (
        @(posedge clk) error_flag
    );
    
    // ============================================
    // TIMING REACHABILITY
    // ============================================
    
    // Cover: Quick completion (within 5 cycles)
    sequence quick_completion;
        (state == IDLE) ##[1:5] (state == DONE);
    endsequence
    
    c_quick: cover property (@(posedge clk) quick_completion);
    
    // Cover: Slow completion (many cycles)
    sequence slow_completion;
        (state == IDLE) ##[20:$] (state == DONE);
    endsequence
    
    c_slow: cover property (@(posedge clk) slow_completion);
    
    // Cover: Stay in state for extended period
    c_long_active: cover property (
        @(posedge clk) (state == ACTIVE)[*10]
    );
    
    // ============================================
    // EDGE CASES REACHABILITY
    // ============================================
    
    // Cover: Reset during operation
    c_reset_during_active: cover property (
        @(posedge clk) (state == ACTIVE) ##1 !rst_n
    );
    
    // Cover: Immediate transition
    c_immediate: cover property (
        @(posedge clk) (state == IDLE) ##1 (state == DONE)
    );
    
    // Cover: Multiple loops through FSM
    c_two_iterations: cover property (
        @(posedge clk) 
        (state == IDLE) ##[1:$] (state == DONE) ##1
        (state == IDLE) ##[1:$] (state == DONE)
    );
    
    // ============================================
    // CONCURRENT CONDITION REACHABILITY
    // ============================================
    
    // Cover: Specific state + counter value
    c_active_counter_high: cover property (
        @(posedge clk) (state == ACTIVE) && (counter > 200)
    );
    
    c_proc_counter_low: cover property (
        @(posedge clk) (state == PROC) && (counter < 50)
    );
    
    // Cover: State + flags
    c_active_busy: cover property (
        @(posedge clk) (state == ACTIVE) && busy
    );
    
    c_done_error: cover property (
        @(posedge clk) (state == DONE) && error_flag
    );

endmodule

// ============================================
// PROTOCOL REACHABILITY
// ============================================

module protocol_reachability_cover (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic ready,
    input logic [31:0] data
);

    // Cover: Transfer happens
    c_transfer: cover property (
        @(posedge clk) valid && ready
    );
    
    // Cover: Valid waits for ready
    c_wait_1: cover property (
        @(posedge clk) valid && !ready ##1 valid && !ready ##1 valid && ready
    );
    
    // Cover: Ready before valid (speculative)
    c_ready_early: cover property (
        @(posedge clk) !valid && ready ##1 valid && ready
    );
    
    // Cover: Back-to-back transfers
    c_back_to_back: cover property (
        @(posedge clk) (valid && ready)[*5]
    );
    
    // Cover: Specific data values
    c_data_zero: cover property (
        @(posedge clk) valid && (data == 0)
    );
    
    c_data_max: cover property (
        @(posedge clk) valid && (data == 32'hFFFFFFFF)
    );
    
    c_data_pattern: cover property (
        @(posedge clk) valid && (data == 32'hDEADBEEF)
    );

endmodule

// ============================================
// WHY COVER PROPERTIES MATTER
// ============================================

/*
 * Cover properties are essential for:
 *
 * 1. VACUITY CHECKING
 *    - Assertion might pass vacuously (never triggered)
 *    - Cover ensures property actually exercises
 *    - Example: "If A then B" passes if A never happens!
 *
 * 2. COMPLETENESS
 *    - Verify all states/transitions reachable
 *    - Find dead code or unreachable states
 *    - Ensure design functionality
 *
 * 3. ASSUMPTION VALIDATION
 *    - Check assumptions aren't too restrictive
 *    - If cover unreachable, assumptions too tight
 *    - Balance constraints vs coverage
 *
 * 4. CORNER CASE DISCOVERY
 *    - Find interesting scenarios
 *    - Identify test cases for simulation
 *    - Understand design capabilities
 *
 * 5. DEBUGGING
 *    - Witness traces show how to reach states
 *    - Use for testbench development
 *    - Understand design behavior
 *
 * Best Practices:
 *   - Add cover for every assertion's antecedent
 *   - Cover boundary conditions
 *   - Cover error paths
 *   - Cover combinations of conditions
 *   - Use covers to generate interesting tests
 *
 * Common Issues:
 *   - Unreachable cover = over-constrained or bug
 *   - All covers trivial = under-tested
 *   - No covers = can't verify assertions exercise
 */
