// ============================================================================
// transition_bins.sv - State Transition Coverage (Sequence Bins)
// ============================================================================

module transition_bins;
    
    // ========================================================================
    // Basic Transition Coverage
    // ========================================================================
    
    typedef enum bit [1:0] {IDLE, ACTIVE, WAIT, DONE} state_e;
    
    class basic_transitions;
        state_e current_state;
        state_e prev_state;
        
        covergroup cg;
            cp_state: coverpoint current_state {
                bins idle = {IDLE};
                bins active = {ACTIVE};
                bins wait_st = {WAIT};
                bins done = {DONE};
                
                // Single transition: from -> to
                bins idle_to_active = (IDLE => ACTIVE);
                bins active_to_wait = (ACTIVE => WAIT);
                bins wait_to_done = (WAIT => DONE);
                bins done_to_idle = (DONE => IDLE);
                
                // Back to back same state
                bins idle_stay = (IDLE => IDLE);
            }
        endgroup
        
        function new();
            cg = new();
            current_state = IDLE;
            prev_state = IDLE;
        endfunction
        
        function void next_state(state_e new_state);
            prev_state = current_state;
            current_state = new_state;
            cg.sample();
        endfunction
    endclass
    
    // ========================================================================
    // Multi-Step Transitions
    // ========================================================================
    
    class multi_step_transitions;
        rand bit [1:0] state;
        
        covergroup cg;
            cp_state: coverpoint state {
                // Two-step sequence
                bins seq_012 = (0 => 1 => 2);
                bins seq_123 = (1 => 2 => 3);
                
                // Three-step sequence
                bins seq_0123 = (0 => 1 => 2 => 3);
                
                // Cycle
                bins cycle = (0 => 1 => 2 => 3 => 0);
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Transitions with Ranges
    // ========================================================================
    
    class range_transitions;
        rand bit [2:0] value;
        
        covergroup cg;
            cp_value: coverpoint value {
                // From range to specific value
                bins low_to_high = ([0:3] => [4:7]);
                
                // From specific to range
                bins zero_to_any = (0 => [1:7]);
                
                // Any to specific
                bins any_to_zero = ([1:7] => 0);
                
                // Range to range
                bins mid_to_high = ([2:4] => [5:7]);
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Repetition Operators
    // ========================================================================
    
    class repetition_transitions;
        rand bit [1:0] value;
        
        covergroup cg;
            cp_value: coverpoint value {
                // Repeat exactly N times: [*N]
                bins stay_at_0_3_times = (0[*3]);  // 0,0,0
                
                // Repeat N to M times: [*N:M]
                bins stay_at_1 = (1[*2:4]);  // 1,1 or 1,1,1 or 1,1,1,1
                
                // Repeat at least once: [+]
                bins ones_then_zero = (1[+] => 0);  // 1+ then 0
                
                // Repeat zero or more: [*]
                bins zeros_then_one = (0[*] => 1);  // 0* then 1
                
                // Consecutive occurrences
                bins two_threes = (3[*2]);  // 3,3
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Goto Repetition (Non-Consecutive)
    // ========================================================================
    
    class goto_transitions;
        rand bit [2:0] value;
        
        covergroup cg;
            cp_value: coverpoint value {
                // Go-to repetition [->N]: non-consecutive occurrences
                // Match N occurrences, but other values can occur in between
                bins three_zeros = (0[->3]);  // 0 occurs 3 times (not necessarily consecutive)
                
                // Example matches: 0,1,0,2,0  or  0,0,0  or  1,0,2,0,3,0
                
                // Go-to followed by transition
                bins zeros_then_seven = (0[->2] => 7);  // 2 zeros (any spacing) then 7
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Complex State Machine Transitions
    // ========================================================================
    
    typedef enum bit [2:0] {
        RESET, IDLE, CONFIG, ACTIVE, PAUSE, ERROR, DONE, SHUTDOWN
    } fsm_state_e;
    
    class fsm_transitions;
        fsm_state_e state;
        
        covergroup cg;
            cp_state: coverpoint state {
                // Valid state bins
                bins reset_st = {RESET};
                bins idle_st = {IDLE};
                bins config_st = {CONFIG};
                bins active_st = {ACTIVE};
                bins pause_st = {PAUSE};
                bins error_st = {ERROR};
                bins done_st = {DONE};
                bins shutdown_st = {SHUTDOWN};
                
                // Normal startup sequence
                bins startup = (RESET => IDLE => CONFIG => ACTIVE);
                
                // Normal shutdown sequence
                bins shutdown = (ACTIVE => DONE => SHUTDOWN);
                
                // Pause/resume
                bins pause_resume = (ACTIVE => PAUSE => ACTIVE);
                
                // Error recovery
                bins error_recovery = (ERROR => RESET => IDLE);
                
                // Multiple pause/resume cycles
                bins multiple_pauses = (ACTIVE => PAUSE[*2:4] => ACTIVE);
                
                // Error from any active state
                bins to_error = ([CONFIG:DONE] => ERROR);
                
                // Back to idle
                bins back_to_idle = ([CONFIG:SHUTDOWN] => IDLE);
                
                // Illegal: can't go directly from RESET to ACTIVE
                illegal_bins bad_reset = (RESET => ACTIVE);
                
                // Illegal: can't stay in ERROR
                illegal_bins stuck_error = (ERROR[*2]);
            }
        endgroup
        
        function new();
            cg = new();
            state = RESET;
        endfunction
        
        function void transition_to(fsm_state_e new_state);
            state = new_state;
            cg.sample();
        endfunction
    endclass
    
    // ========================================================================
    // Protocol Handshake Transitions
    // ========================================================================
    
    class handshake_transitions;
        bit req;
        bit ack;
        bit [1:0] combined;
        
        covergroup cg;
            // Combine req and ack into single value for transition tracking
            cp_handshake: coverpoint combined {
                // State encoding: {req, ack}
                bins idle = {2'b00};
                bins req_only = {2'b10};
                bins ack_only = {2'b01};  // Should not happen
                bins both = {2'b11};
                
                // Normal handshake: idle -> req -> both -> idle
                bins normal_handshake = (2'b00 => 2'b10 => 2'b11 => 2'b00);
                
                // Fast handshake: req and ack in same cycle
                bins fast_handshake = (2'b00 => 2'b11 => 2'b00);
                
                // Slow handshake: req held for multiple cycles
                bins slow_handshake = (2'b00 => 2'b10[*2:5] => 2'b11 => 2'b00);
                
                // Illegal: ack without req
                illegal_bins ack_without_req = (2'b00 => 2'b01);
            }
        endgroup
        
        function new();
            cg = new();
            req = 0;
            ack = 0;
            combined = 0;
        endfunction
        
        function void sample_handshake(bit r, bit a);
            req = r;
            ack = a;
            combined = {req, ack};
            cg.sample();
        endfunction
    endclass
    
    // ========================================================================
    // Burst Transfer Patterns
    // ========================================================================
    
    typedef enum bit [1:0] {IDLE_B, SINGLE, BURST_START, BURST_CONT} burst_state_e;
    
    class burst_patterns;
        burst_state_e state;
        
        covergroup cg;
            cp_burst: coverpoint state {
                // Single transfer
                bins single_xfer = (IDLE_B => SINGLE => IDLE_B);
                
                // Short burst (2-4 beats)
                bins short_burst = (IDLE_B => BURST_START => BURST_CONT[*1:3] => IDLE_B);
                
                // Medium burst (5-8 beats)
                bins medium_burst = (IDLE_B => BURST_START => BURST_CONT[*4:7] => IDLE_B);
                
                // Long burst (9+ beats)
                bins long_burst = (IDLE_B => BURST_START => BURST_CONT[*8:15] => IDLE_B);
                
                // Back-to-back bursts
                bins b2b_bursts = (IDLE_B => BURST_START => BURST_CONT[+] => 
                                  IDLE_B => BURST_START);
                
                // Mixed: single then burst
                bins single_then_burst = (SINGLE => IDLE_B => BURST_START);
            }
        endgroup
        
        function new();
            cg = new();
            state = IDLE_B;
        endfunction
        
        function void next(burst_state_e s);
            state = s;
            cg.sample();
        endfunction
    endclass
    
    // ========================================================================
    // Real-World: AXI Channel Transitions
    // ========================================================================
    
    class axi_channel_transitions;
        bit awvalid;
        bit awready;
        bit wvalid;
        bit wready;
        bit bvalid;
        bit bready;
        bit [2:0] write_phase;  // Encoded state
        
        // Phase encoding: {awvalid&awready, wvalid&wready, bvalid&bready}
        
        covergroup cg;
            cp_write_phase: coverpoint write_phase {
                // Normal write: AW -> W -> B
                bins normal_write = (3'b000 => 3'b100 => 3'b010 => 3'b001 => 3'b000);
                
                // Fast write: all channels ready
                bins fast_write = (3'b000 => 3'b111 => 3'b000);
                
                // AW and W together, then B
                bins aw_w_together = (3'b000 => 3'b110 => 3'b001 => 3'b000);
                
                // W before AW (legal in AXI)
                bins w_before_aw = (3'b000 => 3'b010 => 3'b100 => 3'b001 => 3'b000);
                
                // Slow B response
                bins slow_response = (3'b110 => 3'b000[*2:5] => 3'b001 => 3'b000);
                
                // Back-to-back writes
                bins pipelined_writes = (3'b001 => 3'b100);  // B then immediately next AW
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
        
        function void sample_channels(bit awv, bit awr, bit wv, bit wr, bit bv, bit br);
            awvalid = awv; awready = awr;
            wvalid = wv; wready = wr;
            bvalid = bv; bready = br;
            
            write_phase = {(awvalid & awready), (wvalid & wready), (bvalid & bready)};
            cg.sample();
        endfunction
    endclass
    
    initial begin
        basic_transitions basic;
        multi_step_transitions multi;
        range_transitions ranges;
        repetition_transitions rep;
        fsm_transitions fsm;
        handshake_transitions handshake;
        burst_patterns burst;
        axi_channel_transitions axi;
        
        $display("=== Transition Coverage Examples ===\n");
        
        // Basic transitions
        $display("--- Basic State Transitions ---");
        basic = new();
        basic.next_state(IDLE);
        basic.next_state(ACTIVE);
        basic.next_state(WAIT);
        basic.next_state(DONE);
        basic.next_state(IDLE);
        basic.next_state(ACTIVE);
        $display("Coverage: %0.2f%%", basic.cg.get_coverage());
        
        // Multi-step
        $display("\n--- Multi-Step Transitions ---");
        multi = new();
        repeat(200) begin
            assert(multi.randomize());
            multi.cg.sample();
        end
        $display("Coverage: %0.2f%%", multi.cg.get_coverage());
        
        // FSM
        $display("\n--- FSM Transitions ---");
        fsm = new();
        // Startup
        fsm.transition_to(RESET);
        fsm.transition_to(IDLE);
        fsm.transition_to(CONFIG);
        fsm.transition_to(ACTIVE);
        // Pause/resume
        fsm.transition_to(PAUSE);
        fsm.transition_to(ACTIVE);
        // Shutdown
        fsm.transition_to(DONE);
        fsm.transition_to(SHUTDOWN);
        $display("Coverage: %0.2f%%", fsm.cg.get_coverage());
        
        // Handshake
        $display("\n--- Handshake Transitions ---");
        handshake = new();
        // Normal handshake
        handshake.sample_handshake(0, 0);  // idle
        handshake.sample_handshake(1, 0);  // req
        handshake.sample_handshake(1, 1);  // both
        handshake.sample_handshake(0, 0);  // idle
        // Fast handshake
        handshake.sample_handshake(0, 0);
        handshake.sample_handshake(1, 1);
        handshake.sample_handshake(0, 0);
        $display("Coverage: %0.2f%%", handshake.cg.get_coverage());
        
        // Burst
        $display("\n--- Burst Patterns ---");
        burst = new();
        // Single
        burst.next(IDLE_B);
        burst.next(SINGLE);
        burst.next(IDLE_B);
        // Short burst
        burst.next(BURST_START);
        burst.next(BURST_CONT);
        burst.next(BURST_CONT);
        burst.next(IDLE_B);
        // Long burst
        burst.next(BURST_START);
        repeat(10) burst.next(BURST_CONT);
        burst.next(IDLE_B);
        $display("Coverage: %0.2f%%", burst.cg.get_coverage());
    end
    
endmodule

/*
 * TRANSITION COVERAGE SYNTAX:
 * 
 * SINGLE TRANSITION:
 *   bins name = (val1 => val2);
 * 
 * MULTI-STEP:
 *   bins name = (val1 => val2 => val3);
 * 
 * RANGE TRANSITIONS:
 *   bins name = ([range1] => [range2]);
 * 
 * REPETITION:
 *   [*N]    - Exactly N consecutive times
 *   [*N:M]  - Between N and M consecutive times
 *   [+]     - One or more consecutive times
 *   [*]     - Zero or more consecutive times
 *   [->N]   - N occurrences (non-consecutive, "goto")
 *   [=N]    - N occurrences, end on last (non-consecutive)
 * 
 * EXAMPLES:
 *   (0 => 1 => 2)           - Sequence 0,1,2
 *   (0[*3])                 - 0,0,0
 *   (0[+] => 1)             - One or more 0s, then 1
 *   (0[->3])                - Three 0s (can have other values between)
 *   ([0:3] => [4:7])        - Low range to high range
 * 
 * KEY CONCEPTS:
 * 1. Consecutive: [*N], [+], [*] - no other values between
 * 2. Non-consecutive: [->N], [=N] - other values allowed between
 * 3. Transitions track sequences across samples
 * 4. Need consecutive samples to track transitions
 * 5. Sample at every state change for accurate tracking
 * 
 * WHEN TO USE:
 * - State machine verification
 * - Protocol sequences (handshakes, bursts)
 * - Ordering constraints (A before B)
 * - Temporal patterns
 * - Recovery sequences
 * 
 * WHAT TO COVER:
 * - All valid state transitions
 * - Multi-step sequences (startup, shutdown)
 * - Cycles (return to same state)
 * - Error recovery paths
 * - Rare but valid sequences
 * 
 * BEST PRACTICES:
 * 1. Sample at every state change
 * 2. Use illegal_bins for invalid transitions
 * 3. Cover important multi-step sequences
 * 4. Use repetition for variable-length patterns
 * 5. Combine with regular bins for state coverage
 * 6. Keep sequences reasonable length (not too long)
 * 
 * COMMON PATTERNS:
 * - Normal flow: (IDLE => ACTIVE => DONE => IDLE)
 * - Error recovery: ([any] => ERROR => RESET => IDLE)
 * - Repeated states: (BUSY[*2:10])
 * - Optional states: (A => B[*] => C)  // B is optional
 */
