// Cover Properties for Corner Cases
// Ensures interesting and unusual scenarios are reachable

module corner_case_coverage (
    input logic        clk,
    input logic        rst_n,
    
    // FIFO interface
    input logic        push,
    input logic        pop,
    input logic        full,
    input logic        empty,
    input logic [31:0] wr_data,
    input logic [31:0] rd_data,
    input logic [4:0]  count,
    
    // Arbiter interface
    input logic [3:0]  req,
    input logic [3:0]  grant,
    
    // State machine
    input logic [2:0]  state
);

    // ============================================
    // FIFO CORNER CASES
    // ============================================
    
    // Corner 1: FIFO exactly one entry (almost full and almost empty)
    c_one_entry: cover property (
        @(posedge clk) (count == 1)
    );
    
    // Corner 2: FIFO fills completely from empty in minimum cycles
    sequence rapid_fill;
        empty ##1 (!empty && !full)[*3] ##1 full;
    endsequence
    
    c_rapid_fill: cover property (@(posedge clk) rapid_fill);
    
    // Corner 3: FIFO drains completely in one continuous sequence
    sequence continuous_drain;
        full ##1 (pop && !empty)[*16] ##1 empty;
    endsequence
    
    c_continuous_drain: cover property (@(posedge clk) continuous_drain);
    
    // Corner 4: Simultaneous push/pop when exactly half full
    c_half_full_simul: cover property (
        @(posedge clk) push && pop && (count == 8)
    );
    
    // Corner 5: Push and pop alternate
    sequence alternating_ops;
        push ##1 pop ##1 push ##1 pop ##1 push;
    endsequence
    
    c_alternating: cover property (@(posedge clk) alternating_ops);
    
    // Corner 6: Same data written consecutively
    c_same_data: cover property (
        @(posedge clk) push && (wr_data == 32'hAAAAAAAA) ##1
                       push && (wr_data == 32'hAAAAAAAA)
    );
    
    // Corner 7: Data pattern: zero, max, alternating
    c_data_zero: cover property (@(posedge clk) push && (wr_data == 0));
    c_data_max:  cover property (@(posedge clk) push && (wr_data == 32'hFFFFFFFF));
    c_data_alt:  cover property (@(posedge clk) push && (wr_data == 32'hAAAAAAAA));
    c_data_0x55: cover property (@(posedge clk) push && (wr_data == 32'h55555555));
    
    // Corner 8: Push when almost full becomes full
    c_almost_to_full: cover property (
        @(posedge clk) !full && (count == 15) && push ##1 full
    );
    
    // Corner 9: Pop when almost empty becomes empty
    c_almost_to_empty: cover property (
        @(posedge clk) !empty && (count == 1) && pop ##1 empty
    );
    
    // ============================================
    // ARBITER CORNER CASES
    // ============================================
    
    // Corner 10: All request simultaneously
    c_all_req: cover property (
        @(posedge clk) (req == 4'b1111)
    );
    
    // Corner 11: Only one requester
    c_single_req_0: cover property (@(posedge clk) (req == 4'b0001));
    c_single_req_1: cover property (@(posedge clk) (req == 4'b0010));
    c_single_req_2: cover property (@(posedge clk) (req == 4'b0100));
    c_single_req_3: cover property (@(posedge clk) (req == 4'b1000));
    
    // Corner 12: Grant all four in sequence
    sequence grant_sequence;
        (grant == 4'b0001) ##[1:3]
        (grant == 4'b0010) ##[1:3]
        (grant == 4'b0100) ##[1:3]
        (grant == 4'b1000);
    endsequence
    
    c_grant_seq: cover property (@(posedge clk) grant_sequence);
    
    // Corner 13: Request comes and goes before grant
    c_req_gone: cover property (
        @(posedge clk) req[0] ##1 !req[0] ##[1:5] grant[0]
    );
    
    // Corner 14: No requests for extended period
    c_idle_period: cover property (
        @(posedge clk) (req == 0)[*10]
    );
    
    // ============================================
    // STATE MACHINE CORNER CASES
    // ============================================
    
    // Corner 15: Immediate return to same state
    c_state_loop: cover property (
        @(posedge clk) (state == 3'b010) ##1 (state == 3'b010)
    );
    
    // Corner 16: Skip intermediate states
    c_state_skip: cover property (
        @(posedge clk) (state == 3'b000) ##1 (state == 3'b011)
    );
    
    // Corner 17: Longest path through FSM
    sequence longest_path;
        (state == 3'b000) ##1
        (state == 3'b001) ##[1:10]
        (state == 3'b010) ##[1:10]
        (state == 3'b011) ##[1:10]
        (state == 3'b100);
    endsequence
    
    c_longest: cover property (@(posedge clk) longest_path);
    
    // Corner 18: Shortest path through FSM
    sequence shortest_path;
        (state == 3'b000) ##1
        (state == 3'b001) ##1
        (state == 3'b100);
    endsequence
    
    c_shortest: cover property (@(posedge clk) shortest_path);
    
    // ============================================
    // TIMING CORNER CASES
    // ============================================
    
    // Corner 19: Maximum consecutive operations
    c_max_consec_push: cover property (
        @(posedge clk) (push && !full)[*16]
    );
    
    c_max_consec_pop: cover property (
        @(posedge clk) (pop && !empty)[*16]
    );
    
    // Corner 20: Minimum gap between operations
    c_min_gap: cover property (
        @(posedge clk) push ##10 push
    );
    
    // ============================================
    // ERROR CONDITION REACHABILITY
    // ============================================
    
    // Corner 21: Reach error state
    c_error_reached: cover property (
        @(posedge clk) state == 3'b101
    );
    
    // Corner 22: Error flag sets
    c_error_flag: cover property (
        @(posedge clk) $rose(error_flag)
    );
    
    // Corner 23: Recover from error
    c_error_clear: cover property (
        @(posedge clk) error_flag ##[1:10] !error_flag
    );
    
    // ============================================
    // DATA VALUE CORNER CASES
    // ============================================
    
    // Corner 24: All bits zero
    c_all_zero: cover property (
        @(posedge clk) push && (wr_data == 32'h00000000)
    );
    
    // Corner 25: All bits one
    c_all_ones: cover property (
        @(posedge clk) push && (wr_data == 32'hFFFFFFFF)
    );
    
    // Corner 26: Single bit set
    c_one_bit: cover property (
        @(posedge clk) push && $onehot(wr_data)
    );
    
    // Corner 27: MSB set
    c_msb_set: cover property (
        @(posedge clk) push && wr_data[31]
    );
    
    // Corner 28: LSB set
    c_lsb_set: cover property (
        @(posedge clk) push && wr_data[0]
    );
    
    // ============================================
    // COMBINATORIAL CORNER CASES
    // ============================================
    
    // Corner 29: Multiple rare conditions simultaneously
    c_rare_combo: cover property (
        @(posedge clk) (state == 3'b011) && (count == 1) && error_flag
    );
    
    // Corner 30: Transition during specific count
    c_trans_at_count: cover property (
        @(posedge clk) (state == 3'b010) && (count == 7) ##1 (state == 3'b011)
    );

endmodule

// ============================================
// BUS PROTOCOL CORNER CASES
// ============================================

module bus_protocol_corner_cases (
    input logic        clk,
    input logic        rst_n,
    input logic        valid,
    input logic        ready,
    input logic [31:0] addr,
    input logic [31:0] data,
    input logic        last,
    input logic [2:0]  burst_type
);

    // Corner: Single-beat burst
    c_single_beat: cover property (
        @(posedge clk) valid && ready && last
    );
    
    // Corner: Maximum length burst
    c_max_burst: cover property (
        @(posedge clk) (valid && ready && !last)[*256] ##1 (valid && ready && last)
    );
    
    // Corner: Misaligned address
    c_misalign: cover property (
        @(posedge clk) valid && (addr[1:0] != 2'b00)
    );
    
    // Corner: Address wrap-around
    c_addr_wrap: cover property (
        @(posedge clk) valid && (addr == 32'hFFFFFFFC) ##1 
                       valid && (addr == 32'h00000000)
    );
    
    // Corner: Each burst type
    c_fixed:  cover property (@(posedge clk) valid && (burst_type == 3'b000));
    c_incr:   cover property (@(posedge clk) valid && (burst_type == 3'b001));
    c_wrap:   cover property (@(posedge clk) valid && (burst_type == 3'b010));

endmodule

// ============================================
// USAGE TIPS
// ============================================

/*
 * How to use corner case covers:
 *
 * 1. IDENTIFY CORNER CASES
 *    - Boundary values (0, max, overflow)
 *    - Flag combinations
 *    - Rare state combinations
 *    - Timing extremes (min/max delays)
 *    - Error conditions
 *
 * 2. WRITE COVERS
 *    - Be specific (not too general)
 *    - Focus on interesting cases
 *    - Combine multiple conditions
 *
 * 3. RUN FORMAL
 *    - Check which covers pass
 *    - Unreachable covers indicate:
 *      * Over-constrained assumptions
 *      * Design limitation
 *      * Impossible scenario
 *
 * 4. ANALYZE RESULTS
 *    - Reachable: Good, design can handle it
 *    - Unreachable: Investigate why
 *    - Use witness traces for test generation
 *
 * 5. ITERATE
 *    - Relax assumptions if needed
 *    - Add more corner cases
 *    - Generate simulation tests from witnesses
 *
 * Example workflow:
 *   1. Write assertion: "full |-> !push"
 *   2. Write cover: "full" (verify full is reachable)
 *   3. Run formal
 *   4. If cover fails, full state unreachable - check why
 *   5. If cover passes, assertion is meaningful
 */
