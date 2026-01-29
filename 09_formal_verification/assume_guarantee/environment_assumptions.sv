// Environment Assumptions for Formal Verification
// Constrains inputs to reasonable/legal behaviors

module environment_assumptions (
    input logic        clk,
    input logic        rst_n,
    
    // Request-acknowledge interface
    input logic        req,
    input logic        ack,
    
    // Valid-ready interface
    input logic        valid,
    input logic        ready,
    input logic [31:0] data,
    
    // Control signals
    input logic        start,
    input logic        stop,
    
    // Configuration
    input logic [7:0]  config
);

    // ============================================
    // REQUEST-ACKNOWLEDGE ASSUMPTIONS
    // ============================================
    
    // Assume 1: Request stays high until acknowledged
    property req_stable;
        @(posedge clk) disable iff (!rst_n)
        req && !ack |=> req;
    endproperty
    
    assume_req_stable: assume property (req_stable);
    
    // Assume 2: Request drops after acknowledge
    property req_drops_after_ack;
        @(posedge clk) disable iff (!rst_n)
        req && ack |=> !req;
    endproperty
    
    assume_req_protocol: assume property (req_drops_after_ack);
    
    // Assume 3: No new request immediately after previous
    property req_gap;
        @(posedge clk) disable iff (!rst_n)
        $fell(req) |-> ##[1:$] req;  // At least 1 cycle gap
    endproperty
    
    assume_req_spacing: assume property (req_gap);
    
    // Assume 4: Request eventually deasserts (for liveness)
    property req_eventually_drops;
        @(posedge clk) disable iff (!rst_n)
        req |-> ##[1:100] !req;
    endproperty
    
    assume_req_bounded: assume property (req_eventually_drops);
    
    // ============================================
    // VALID-READY ASSUMPTIONS
    // ============================================
    
    // Assume 5: Valid obeys handshake protocol
    property valid_stable_assumption;
        @(posedge clk) disable iff (!rst_n)
        valid && !ready |=> valid;
    endproperty
    
    assume_valid_stable: assume property (valid_stable_assumption);
    
    // Assume 6: Data stable during valid
    property data_stable_assumption;
        @(posedge clk) disable iff (!rst_n)
        valid && !ready |=> $stable(data);
    endproperty
    
    assume_data_stable: assume property (data_stable_assumption);
    
    // Assume 7: Ready doesn't depend combinationally on valid
    // (prevents combinational loops)
    property ready_registered;
        @(posedge clk) disable iff (!rst_n)
        $rose(valid) |-> $stable(ready);  // Ready already decided
    endproperty
    
    // This might be too strict for some designs
    // assume_ready_timing: assume property (ready_registered);
    
    // ============================================
    // DATA VALUE ASSUMPTIONS
    // ============================================
    
    // Assume 8: Data is defined (no X/Z)
    property data_defined;
        @(posedge clk) disable iff (!rst_n)
        valid |-> !$isunknown(data);
    endproperty
    
    assume_data_clean: assume property (data_defined);
    
    // Assume 9: Data within reasonable range (if applicable)
    property data_reasonable;
        @(posedge clk) disable iff (!rst_n)
        valid |-> (data < 32'h0000_1000);  // Example: addresses below 4K
    endproperty
    
    // assume_data_range: assume property (data_reasonable);
    
    // Assume 10: Certain bit patterns never occur
    property no_all_ones;
        @(posedge clk) disable iff (!rst_n)
        valid |-> (data != 32'hFFFFFFFF);
    endproperty
    
    // assume_no_special: assume property (no_all_ones);
    
    // ============================================
    // TIMING ASSUMPTIONS
    // ============================================
    
    // Assume 11: Reset asserted for minimum duration
    property reset_duration;
        @(posedge clk)
        $fell(rst_n) |-> ##[5:$] rst_n;
    endproperty
    
    assume_reset_time: assume property (reset_duration);
    
    // Assume 12: Reset not asserted during operation
    property no_random_reset;
        @(posedge clk)
        (valid || req) |-> rst_n;
    endproperty
    
    assume_clean_reset: assume property (no_random_reset);
    
    // Assume 13: Bounded transaction rate
    property max_transaction_rate;
        @(posedge clk) disable iff (!rst_n)
        valid |-> ##[3:$] valid;  // At least 3 cycles between
    endproperty
    
    // assume_rate_limit: assume property (max_transaction_rate);
    
    // ============================================
    // CONTROL SIGNAL ASSUMPTIONS
    // ============================================
    
    // Assume 14: Start and stop are mutually exclusive
    property start_stop_mutex;
        @(posedge clk) disable iff (!rst_n)
        !(start && stop);
    endproperty
    
    assume_ctrl_mutex: assume property (start_stop_mutex);
    
    // Assume 15: Start is one-cycle pulse
    property start_pulse;
        @(posedge clk) disable iff (!rst_n)
        start |=> !start;
    endproperty
    
    assume_start_timing: assume property (start_pulse);
    
    // Assume 16: Configuration stable during operation
    property config_stable;
        @(posedge clk) disable iff (!rst_n)
        (valid || req) |-> $stable(config);
    endproperty
    
    assume_config_stable: assume property (config_stable);
    
    // ============================================
    // FAIRNESS ASSUMPTIONS
    // ============================================
    
    // Assume 17: Environment is fair (for liveness proofs)
    property fair_environment;
        @(posedge clk) disable iff (!rst_n)
        req |-> ##[1:50] ack;  // Environment eventually responds
    endproperty
    
    assume_fairness: assume property (fair_environment);
    
    // Assume 18: Not infinitely fast
    property not_infinite_rate;
        @(posedge clk) disable iff (!rst_n)
        valid && ready |-> ##1 (!valid || !ready);  // Can't sustain every cycle forever
    endproperty
    
    // assume_realistic_rate: assume property (not_infinite_rate);
    
    // ============================================
    // PROTOCOL-SPECIFIC ASSUMPTIONS
    // ============================================
    
    // For AXI: Assume master follows protocol
    // For APB: Assume controller follows protocol
    // For memory: Assume addresses in range
    
    // Example: Memory address assumptions
    property addr_in_range;
        @(posedge clk) disable iff (!rst_n)
        valid |-> (data[31:12] == 20'h0);  // Only low 4KB used
    endproperty
    
    // assume_addr_range: assume property (addr_in_range);

endmodule

// ============================================
// ASSUMPTIONS FOR SPECIFIC DUT TYPES
// ============================================

module fifo_environment_assumptions (
    input logic clk,
    input logic rst_n,
    input logic push,
    input logic pop,
    input logic full,
    input logic empty
);

    // Assume: Well-behaved pusher
    assume property (@(posedge clk) disable iff (!rst_n)
        full |-> !push
    );
    
    // Assume: Well-behaved popper
    assume property (@(posedge clk) disable iff (!rst_n)
        empty |-> !pop
    );
    
    // Assume: Not idle forever (for liveness)
    assume property (@(posedge clk) disable iff (!rst_n)
        !full |-> ##[1:20] (push || full)
    );

endmodule

module arbiter_environment_assumptions (
    input logic clk,
    input logic rst_n,
    input logic [3:0] req,
    input logic [3:0] grant
);

    // Assume: Requester drops request after grant
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin : gen_assume
            assume property (@(posedge clk) disable iff (!rst_n)
                grant[i] |=> ##[0:5] !req[i]
            );
        end
    endgenerate
    
    // Assume: Not all requesting forever
    assume property (@(posedge clk) disable iff (!rst_n)
        (req == 4'b1111) |-> ##[1:10] (req != 4'b1111)
    );

endmodule

module axi_environment_assumptions (
    input logic        aclk,
    input logic        aresetn,
    input logic        awvalid,
    input logic        awready,
    input logic        wvalid,
    input logic        bready
);

    // Assume: BREADY eventually asserts
    assume property (@(posedge aclk) disable iff (!aresetn)
        1'b1 |-> ##[0:10] bready  // Ready to accept response
    );
    
    // Assume: Write data comes within reasonable time of address
    assume property (@(posedge aclk) disable iff (!aresetn)
        (awvalid && awready) |-> ##[0:20] wvalid
    );

endmodule

// ============================================
// BEST PRACTICES FOR ASSUMPTIONS
// ============================================

/*
 * Guidelines for writing assumptions:
 *
 * 1. REASONABLENESS
 *    - Assumptions should reflect real environment
 *    - Don't over-constrain (makes proof trivial)
 *    - Don't under-constrain (state explosion)
 *
 * 2. VALIDATION
 *    - Use covers to verify assumptions are reasonable
 *    - If cover unreachable, assumptions too tight
 *    - If proof trivial, assumptions too strong
 *
 * 3. DOCUMENTATION
 *    - Document why each assumption is needed
 *    - Explain what happens if violated
 *    - Link to specification
 *
 * 4. TYPES OF ASSUMPTIONS
 *    - Protocol: Input follows standard
 *    - Timing: Bounded delays
 *    - Value: Data in valid range
 *    - Fairness: Progress guaranteed
 *
 * 5. VERIFICATION
 *    - Assumptions become requirements for environment
 *    - Must verify in simulation or higher-level proof
 *    - Document in integration specification
 *
 * Example workflow:
 *   1. Start with no assumptions
 *   2. Proof fails or doesn't converge
 *   3. Add minimal assumptions
 *   4. Verify assumptions with covers
 *   5. Document assumptions as requirements
 *
 * Warning signs:
 *   - Too many assumptions = proof not meaningful
 *   - Unrealistic assumptions = doesn't match real use
 *   - Conflicting assumptions = impossible scenario
 *   - Circular assumptions = logical error
 */
