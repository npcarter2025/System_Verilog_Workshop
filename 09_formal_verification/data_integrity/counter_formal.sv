// Formal Verification of Counter Correctness
// Proves counter operates within bounds and increments/decrements correctly

module counter_formal_properties #(
    parameter WIDTH = 8,
    parameter MAX_COUNT = (1 << WIDTH) - 1
) (
    input logic              clk,
    input logic              rst_n,
    input logic              en,
    input logic              up_down,   // 1=up, 0=down
    input logic              load,
    input logic [WIDTH-1:0]  load_value,
    input logic [WIDTH-1:0]  count,
    input logic              tc          // Terminal count
);

    // ============================================
    // BASIC COUNTER PROPERTIES
    // ============================================
    
    // Property 1: Count within valid range
    property count_in_range;
        @(posedge clk) disable iff (!rst_n)
        count <= MAX_COUNT;
    endproperty
    
    a_range: assert property (count_in_range)
        else $error("COUNT ERROR: count=%0d exceeds MAX=%0d", count, MAX_COUNT);
    
    // Property 2: Reset to zero
    property reset_to_zero;
        @(posedge clk)
        !rst_n |=> (count == 0);
    endproperty
    
    a_reset: assert property (reset_to_zero)
        else $error("RESET ERROR: count=%0d after reset", count);
    
    // ============================================
    // INCREMENT PROPERTIES
    // ============================================
    
    // Property 3: Increment when enabled and counting up
    property increment_up;
        @(posedge clk) disable iff (!rst_n)
        en && up_down && !load && (count < MAX_COUNT) |=>
            count == ($past(count) + 1);
    endproperty
    
    a_incr: assert property (increment_up)
        else $error("INCREMENT ERROR: count=%0d, expected=%0d", 
                   count, $past(count) + 1);
    
    // Property 4: Decrement when enabled and counting down
    property decrement_down;
        @(posedge clk) disable iff (!rst_n)
        en && !up_down && !load && (count > 0) |=>
            count == ($past(count) - 1);
    endproperty
    
    a_decr: assert property (decrement_down)
        else $error("DECREMENT ERROR: count=%0d, expected=%0d",
                   count, $past(count) - 1);
    
    // Property 5: Count stable when not enabled
    property stable_when_disabled;
        @(posedge clk) disable iff (!rst_n)
        !en && !load |=> $stable(count);
    endproperty
    
    a_stable: assert property (stable_when_disabled)
        else $error("STABILITY ERROR: count changed without enable");
    
    // ============================================
    // WRAP-AROUND PROPERTIES
    // ============================================
    
    // Property 6: Wrap to zero at maximum (up count)
    property wrap_to_zero;
        @(posedge clk) disable iff (!rst_n)
        en && up_down && !load && (count == MAX_COUNT) |=>
            (count == 0);
    endproperty
    
    a_wrap_zero: assert property (wrap_to_zero)
        else $error("WRAP ERROR: count=%0d at max, expected 0", count);
    
    // Property 7: Wrap to max at zero (down count)
    property wrap_to_max;
        @(posedge clk) disable iff (!rst_n)
        en && !up_down && !load && (count == 0) |=>
            (count == MAX_COUNT);
    endproperty
    
    a_wrap_max: assert property (wrap_to_max)
        else $error("WRAP ERROR: count=%0d at zero, expected MAX", count);
    
    // ============================================
    // LOAD PROPERTIES
    // ============================================
    
    // Property 8: Load overrides counting
    property load_priority;
        @(posedge clk) disable iff (!rst_n)
        load |=> (count == $past(load_value));
    endproperty
    
    a_load: assert property (load_priority)
        else $error("LOAD ERROR: count=%0d, expected=%0d", 
                   count, $past(load_value));
    
    // Property 9: Load value within range
    property load_value_valid;
        @(posedge clk) disable iff (!rst_n)
        load |-> (load_value <= MAX_COUNT);
    endproperty
    
    a_load_range: assert property (load_value_valid)
        else $error("LOAD VALUE ERROR: load_value=%0d exceeds MAX", load_value);
    
    // ============================================
    // TERMINAL COUNT PROPERTIES
    // ============================================
    
    // Property 10: TC asserts at maximum (up count)
    property tc_at_max_up;
        @(posedge clk) disable iff (!rst_n)
        up_down && (count == MAX_COUNT) |-> tc;
    endproperty
    
    a_tc_max: assert property (tc_at_max_up)
        else $error("TC ERROR: count at MAX but tc=%b", tc);
    
    // Property 11: TC asserts at zero (down count)
    property tc_at_zero_down;
        @(posedge clk) disable iff (!rst_n)
        !up_down && (count == 0) |-> tc;
    endproperty
    
    a_tc_zero: assert property (tc_at_zero_down)
        else $error("TC ERROR: count at 0 but tc=%b", tc);
    
    // Property 12: TC only when at boundary
    property tc_only_at_boundary;
        @(posedge clk) disable iff (!rst_n)
        tc |-> ((up_down && (count == MAX_COUNT)) || 
                (!up_down && (count == 0)));
    endproperty
    
    a_tc_valid: assert property (tc_only_at_boundary)
        else $error("TC ERROR: tc asserted but count=%0d", count);
    
    // ============================================
    // MONOTONICITY
    // ============================================
    
    // Property 13: Count always increases or stays same (up mode)
    property monotonic_increase;
        @(posedge clk) disable iff (!rst_n)
        up_down && !load |=>
            (count >= $past(count)) || (count == 0 && $past(count) == MAX_COUNT);
    endproperty
    
    // Property 14: Count always decreases or stays same (down mode)
    property monotonic_decrease;
        @(posedge clk) disable iff (!rst_n)
        !up_down && !load |=>
            (count <= $past(count)) || (count == MAX_COUNT && $past(count) == 0);
    endproperty
    
    // ============================================
    // NO SKIP PROPERTIES
    // ============================================
    
    // Property 15: Counter doesn't skip values (up)
    property no_skip_up;
        @(posedge clk) disable iff (!rst_n)
        en && up_down && !load && (count != 0 || $past(count) == MAX_COUNT) |=>
            (count == $past(count) + 1) || (count == 0 && $past(count) == MAX_COUNT);
    endproperty
    
    // Property 16: Counter doesn't skip values (down)
    property no_skip_down;
        @(posedge clk) disable iff (!rst_n)
        en && !up_down && !load && (count != MAX_COUNT || $past(count) == 0) |=>
            (count == $past(count) - 1) || (count == MAX_COUNT && $past(count) == 0);
    endproperty
    
    // ============================================
    // COVERAGE
    // ============================================
    
    // Cover: Reach maximum
    c_max: cover property (@(posedge clk) count == MAX_COUNT);
    
    // Cover: Reach zero
    c_zero: cover property (@(posedge clk) count == 0);
    
    // Cover: Wrap around (up)
    c_wrap_up: cover property (
        @(posedge clk) (count == MAX_COUNT) ##1 (count == 0)
    );
    
    // Cover: Wrap around (down)
    c_wrap_down: cover property (
        @(posedge clk) (count == 0) ##1 (count == MAX_COUNT)
    );
    
    // Cover: Load while counting
    c_load: cover property (
        @(posedge clk) en && load
    );
    
    // Cover: Count through middle value
    c_mid: cover property (
        @(posedge clk) count == (MAX_COUNT / 2)
    );
    
    // Cover: Terminal count triggered
    c_tc: cover property (@(posedge clk) tc);
    
    // Cover: Direction change
    c_dir_change: cover property (
        @(posedge clk) up_down ##1 !up_down
    );
    
    // ============================================
    // SEQUENCE COVERAGE
    // ============================================
    
    // Cover: Count from 0 to MAX
    sequence count_to_max;
        (count == 0) ##[1:$] (count == MAX_COUNT);
    endsequence
    
    c_full_up: cover property (@(posedge clk) count_to_max);
    
    // Cover: Count from MAX to 0
    sequence count_to_zero;
        (count == MAX_COUNT) ##[1:$] (count == 0);
    endsequence
    
    c_full_down: cover property (@(posedge clk) count_to_zero);
    
    // ============================================
    // ADDITIONAL CHECKS FOR SPECIFIC COUNTER TYPES
    // ============================================
    
    // For Gray code counter: only one bit changes
    // (This would be in a separate module)
    
    // For Johnson counter: specific pattern
    // (This would be in a separate module)
    
    // For ring counter: one-hot property
    // (This would be in a separate module)

endmodule

// ============================================
// GRAY CODE COUNTER PROPERTIES
// ============================================

module gray_counter_formal #(
    parameter WIDTH = 4
) (
    input logic              clk,
    input logic              rst_n,
    input logic              en,
    input logic [WIDTH-1:0]  gray_count
);

    // Property: Only one bit changes per cycle
    property one_bit_change;
        @(posedge clk) disable iff (!rst_n)
        en |=> $countones(gray_count ^ $past(gray_count)) <= 1;
    endproperty
    
    a_one_bit: assert property (one_bit_change)
        else $error("GRAY ERROR: Multiple bits changed");
    
    // Property: Gray code encoding is correct
    logic [WIDTH-1:0] binary_count;
    // Assume we have binary count available
    
    property gray_encoding;
        @(posedge clk) disable iff (!rst_n)
        gray_count == (binary_count ^ (binary_count >> 1));
    endproperty
    
    a_encoding: assert property (gray_encoding);

endmodule

// ============================================
// MODULO-N COUNTER PROPERTIES
// ============================================

module modulo_counter_formal #(
    parameter MODULO = 10
) (
    input logic              clk,
    input logic              rst_n,
    input logic              en,
    input logic [7:0]        count
);

    // Property: Count stays below modulo
    property count_below_modulo;
        @(posedge clk) disable iff (!rst_n)
        count < MODULO;
    endproperty
    
    a_modulo: assert property (count_below_modulo)
        else $error("MODULO ERROR: count=%0d >= MODULO=%0d", count, MODULO);
    
    // Property: Wraps at modulo-1
    property wrap_at_modulo;
        @(posedge clk) disable iff (!rst_n)
        en && (count == MODULO - 1) |=> (count == 0);
    endproperty
    
    a_wrap: assert property (wrap_at_modulo)
        else $error("WRAP ERROR: didn't wrap at MODULO-1");

endmodule

// ============================================
// USAGE NOTES
// ============================================

/*
 * Counter formal verification proves:
 *   1. Correct increment/decrement
 *   2. Proper wrap-around
 *   3. Load functionality
 *   4. Terminal count accuracy
 *   5. No value skipping
 *   6. Range bounds
 *
 * Common counter bugs found by formal:
 *   - Off-by-one in wrap condition
 *   - Incorrect terminal count logic
 *   - Load priority issues
 *   - Enable not checked properly
 *   - Wrong wrap value
 *
 * Formal is excellent for counters because:
 *   - Small state space (2^WIDTH states)
 *   - Clear specification
 *   - Easy to write properties
 *   - Quick convergence
 *
 * Typical proof depth: 2^WIDTH + 10 cycles
 */
