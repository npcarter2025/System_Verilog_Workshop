// Protocol Sequence Coverage
// Covers complex multi-step protocol sequences to ensure they're reachable

module protocol_sequence_coverage (
    input logic        clk,
    input logic        rst_n,
    
    // AXI-like write interface
    input logic        awvalid,
    input logic        awready,
    input logic        wvalid,
    input logic        wready,
    input logic        wlast,
    input logic        bvalid,
    input logic        bready,
    
    // AXI-like read interface
    input logic        arvalid,
    input logic        arready,
    input logic        rvalid,
    input logic        rready,
    input logic        rlast
);

    // ============================================
    // WRITE TRANSACTION SEQUENCES
    // ============================================
    
    // Sequence 1: Simple write (address and data same cycle)
    sequence simple_write;
        (awvalid && awready && wvalid && wready && wlast) ##[1:10]
        (bvalid && bready);
    endsequence
    
    c_simple_write: cover property (@(posedge clk) simple_write);
    
    // Sequence 2: Write with address first
    sequence addr_first_write;
        (awvalid && awready && !wvalid) ##[1:5]
        (wvalid && wready && wlast) ##[1:10]
        (bvalid && bready);
    endsequence
    
    c_addr_first: cover property (@(posedge clk) addr_first_write);
    
    // Sequence 3: Write with data first
    sequence data_first_write;
        (wvalid && !awvalid) ##[1:5]
        (awvalid && awready && wready && wlast) ##[1:10]
        (bvalid && bready);
    endsequence
    
    c_data_first: cover property (@(posedge clk) data_first_write);
    
    // Sequence 4: Multi-beat write burst
    sequence burst_write;
        (awvalid && awready) ##[0:3]
        (wvalid && wready && !wlast)[*3] ##1
        (wvalid && wready && wlast) ##[1:10]
        (bvalid && bready);
    endsequence
    
    c_burst_write: cover property (@(posedge clk) burst_write);
    
    // Sequence 5: Write with back pressure (wait states)
    sequence write_backpressure;
        (awvalid && !awready)[*3] ##1
        (awvalid && awready) ##1
        (wvalid && !wready)[*2] ##1
        (wvalid && wready && wlast) ##[1:10]
        (bvalid && bready);
    endsequence
    
    c_write_backpressure: cover property (@(posedge clk) write_backpressure);
    
    // Sequence 6: Back-to-back writes
    sequence consec_writes;
        (bvalid && bready) ##1 (awvalid && awready);
    endsequence
    
    c_consec_writes: cover property (@(posedge clk) consec_writes);
    
    // ============================================
    // READ TRANSACTION SEQUENCES
    // ============================================
    
    // Sequence 7: Simple read
    sequence simple_read;
        (arvalid && arready) ##[1:10]
        (rvalid && rready && rlast);
    endsequence
    
    c_simple_read: cover property (@(posedge clk) simple_read);
    
    // Sequence 8: Multi-beat read burst
    sequence burst_read;
        (arvalid && arready) ##[1:10]
        (rvalid && rready && !rlast)[*3] ##1
        (rvalid && rready && rlast);
    endsequence
    
    c_burst_read: cover property (@(posedge clk) burst_read);
    
    // Sequence 9: Read with backpressure
    sequence read_backpressure;
        (arvalid && !arready)[*2] ##1
        (arvalid && arready) ##[1:5]
        (rvalid && !rready)[*3] ##1
        (rvalid && rready && rlast);
    endsequence
    
    c_read_backpressure: cover property (@(posedge clk) read_backpressure);
    
    // ============================================
    // MIXED READ/WRITE SEQUENCES
    // ============================================
    
    // Sequence 10: Write followed by read (same address pattern)
    sequence write_then_read;
        (awvalid && awready) ##[1:$] (bvalid && bready) ##[1:5]
        (arvalid && arready);
    endsequence
    
    c_wr_then_rd: cover property (@(posedge clk) write_then_read);
    
    // Sequence 11: Overlapping write and read
    sequence overlapping_wr_rd;
        (awvalid && arvalid);
    endsequence
    
    c_overlap: cover property (@(posedge clk) overlapping_wr_rd);
    
    // Sequence 12: Interleaved transactions
    sequence interleaved;
        (awvalid && awready) ##1
        (arvalid && arready) ##1
        (wvalid && wready && wlast);
    endsequence
    
    c_interleaved: cover property (@(posedge clk) interleaved);
    
    // ============================================
    // ERROR SEQUENCES
    // ============================================
    
    // Sequence 13: Transaction with error response
    // (Assuming bresp signal exists)
    // sequence error_response;
    //     (awvalid && awready) ##[1:$]
    //     (bvalid && bready && (bresp != 2'b00));
    // endsequence
    
    // ============================================
    // TIMING VARIATIONS
    // ============================================
    
    // Sequence 14: Immediate response (no wait)
    sequence zero_wait_write;
        (awvalid && awready && wvalid && wready && wlast) ##1
        (bvalid && bready);
    endsequence
    
    c_zero_wait: cover property (@(posedge clk) zero_wait_write);
    
    // Sequence 15: Maximum wait time
    sequence max_wait_write;
        (awvalid && awready) ##1
        (wvalid && wready && wlast) ##20
        (bvalid && bready);
    endsequence
    
    c_max_wait: cover property (@(posedge clk) max_wait_write);
    
    // ============================================
    // COMPLEX PROTOCOL SCENARIOS
    // ============================================
    
    // Sequence 16: Multiple outstanding transactions
    // (Assuming no reordering)
    sequence outstanding_2;
        (awvalid && awready) ##1
        (awvalid && awready) ##[1:$]
        (bvalid && bready) ##1
        (bvalid && bready);
    endsequence
    
    c_outstanding: cover property (@(posedge clk) outstanding_2);
    
    // Sequence 17: Channel synchronization
    sequence channels_sync;
        (awvalid && awready) ##0
        (wvalid && wready && wlast);
    endsequence
    
    c_sync: cover property (@(posedge clk) channels_sync);

endmodule

// ============================================
// STATE MACHINE PROTOCOL SEQUENCES
// ============================================

module fsm_protocol_sequences (
    input logic [2:0] state,
    input logic clk,
    input logic rst_n
);

    localparam IDLE   = 3'b000;
    localparam SETUP  = 3'b001;
    localparam ACTIVE = 3'b010;
    localparam WAIT   = 3'b011;
    localparam DONE   = 3'b100;
    
    // Cover: Complete sequences
    sequence full_sequence;
        (state == IDLE) ##1
        (state == SETUP) ##1
        (state == ACTIVE) ##[1:$]
        (state == DONE);
    endsequence
    
    c_full: cover property (@(posedge clk) full_sequence);
    
    // Cover: With wait state
    sequence with_wait;
        (state == ACTIVE) ##1
        (state == WAIT)[*1:5] ##1
        (state == ACTIVE);
    endsequence
    
    c_with_wait: cover property (@(posedge clk) with_wait);
    
    // Cover: All possible paths
    c_idle_setup:   cover property (@(posedge clk) (state==IDLE) ##1 (state==SETUP));
    c_setup_active: cover property (@(posedge clk) (state==SETUP) ##1 (state==ACTIVE));
    c_active_wait:  cover property (@(posedge clk) (state==ACTIVE) ##1 (state==WAIT));
    c_wait_active:  cover property (@(posedge clk) (state==WAIT) ##1 (state==ACTIVE));
    c_active_done:  cover property (@(posedge clk) (state==ACTIVE) ##1 (state==DONE));
    c_done_idle:    cover property (@(posedge clk) (state==DONE) ##1 (state==IDLE));

endmodule

// ============================================
// HANDSHAKE PATTERN SEQUENCES
// ============================================

module handshake_pattern_sequences (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic ready
);

    // Pattern 1: Transfer every cycle (full throughput)
    sequence full_throughput;
        (valid && ready)[*10];
    endsequence
    
    c_full_tp: cover property (@(posedge clk) full_throughput);
    
    // Pattern 2: Valid waits for ready (producer slower)
    sequence producer_limited;
        valid && !ready ##1
        valid && !ready ##1
        valid && ready;
    endsequence
    
    c_prod_wait: cover property (@(posedge clk) producer_limited);
    
    // Pattern 3: Ready waits for valid (consumer slower)
    sequence consumer_limited;
        !valid && ready ##1
        !valid && ready ##1
        valid && ready;
    endsequence
    
    c_cons_wait: cover property (@(posedge clk) consumer_limited);
    
    // Pattern 4: Both arrive same cycle
    c_simultaneous: cover property (
        @(posedge clk) !valid && !ready ##1 valid && ready
    );
    
    // Pattern 5: Alternating (transfer every other cycle)
    sequence alternating;
        (valid && ready) ##1
        (!valid || !ready) ##1
        (valid && ready);
    endsequence
    
    c_alternating: cover property (@(posedge clk) alternating);
    
    // Pattern 6: Burst then idle
    sequence burst_idle;
        (valid && ready)[*5] ##1
        (!valid)[*5];
    endsequence
    
    c_burst_idle: cover property (@(posedge clk) burst_idle);

endmodule

// ============================================
// MULTI-MASTER BUS SEQUENCES
// ============================================

module multi_master_sequences (
    input logic        clk,
    input logic        rst_n,
    input logic [1:0]  master_grant,
    input logic        bus_valid,
    input logic        bus_ready
);

    // Sequence: Master 0 gets grant, transfers, releases
    sequence master_0_transfer;
        (master_grant == 2'b01) ##1
        (bus_valid && bus_ready) ##1
        (master_grant == 2'b00);
    endsequence
    
    c_m0_trans: cover property (@(posedge clk) master_0_transfer);
    
    // Sequence: Master switch during transaction
    sequence master_switch;
        (master_grant == 2'b01) ##[1:5]
        (master_grant == 2'b10);
    endsequence
    
    c_m_switch: cover property (@(posedge clk) master_switch);
    
    // Sequence: Round-robin master access
    sequence round_robin_masters;
        (master_grant == 2'b01) ##[1:$]
        (master_grant == 2'b10) ##[1:$]
        (master_grant == 2'b01);
    endsequence
    
    c_round_robin: cover property (@(posedge clk) round_robin_masters);

endmodule

// ============================================
// USAGE NOTES
// ============================================

/*
 * Protocol sequence coverage is essential for:
 *
 * 1. VERIFYING PROTOCOL SUPPORT
 *    - Prove design can handle all valid sequences
 *    - Find unsupported scenarios
 *    - Validate protocol implementation
 *
 * 2. CORNER CASE DISCOVERY
 *    - Complex multi-step scenarios
 *    - Timing variations
 *    - Interleaving patterns
 *
 * 3. TEST GENERATION
 *    - Use witness traces as test cases
 *    - Cover complex scenarios in simulation
 *    - Build regression test suite
 *
 * 4. SPECIFICATION VALIDATION
 *    - Check if spec allows certain sequences
 *    - Find ambiguities in specification
 *    - Document allowed behaviors
 *
 * Best practices:
 *   - Cover happy paths
 *   - Cover error paths
 *   - Cover timing variations
 *   - Cover interleaving
 *   - Cover maximum/minimum lengths
 *   - Cover transitions between sequences
 *
 * If sequence unreachable:
 *   - Check assumptions (too restrictive?)
 *   - Check design (limitation?)
 *   - Check property (impossible?)
 *   - Increase depth bound
 *
 * Use covers to:
 *   - Validate assertions are meaningful
 *   - Generate interesting test cases
 *   - Understand design capabilities
 *   - Find specification gaps
 */
