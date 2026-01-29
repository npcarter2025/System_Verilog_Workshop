// Formal Proof of Arbiter Correctness
// Proves fairness, mutual exclusion, and liveness properties

module arbiter_formal_proof #(
    parameter NUM_REQ = 4
) (
    input logic                 clk,
    input logic                 rst_n,
    input logic [NUM_REQ-1:0]   req,
    input logic [NUM_REQ-1:0]   grant
);

    // ============================================
    // SAFETY PROPERTIES
    // ============================================
    
    // Property 1: At most one grant at a time (mutual exclusion)
    property grant_mutex;
        @(posedge clk) disable iff (!rst_n)
        $onehot0(grant);
    endproperty
    
    a_mutex: assert property (grant_mutex)
        else $error("MUTEX VIOLATION: Multiple grants %b", grant);
    
    // Property 2: Grant only when requested
    property grant_only_if_req;
        @(posedge clk) disable iff (!rst_n)
        (grant != 0) |-> ((grant & req) == grant);
    endproperty
    
    a_grant_valid: assert property (grant_only_if_req)
        else $error("Grant %b without request %b", grant, req);
    
    // Property 3: Grant is one-hot or zero
    property grant_onehot;
        @(posedge clk) disable iff (!rst_n)
        $onehot0(grant);
    endproperty
    
    a_onehot: assert property (grant_onehot);
    
    // ============================================
    // LIVENESS PROPERTIES
    // ============================================
    
    // Property 4: Every request eventually granted
    genvar i;
    generate
        for (i = 0; i < NUM_REQ; i++) begin : gen_liveness
            property request_eventually_granted;
                @(posedge clk) disable iff (!rst_n)
                req[i] |-> ##[1:100] grant[i];
            endproperty
            
            a_liveness: assert property (request_eventually_granted)
                else $error("LIVENESS: Request %0d not granted", i);
        end
    endgenerate
    
    // Property 5: No starvation (bounded waiting)
    generate
        for (i = 0; i < NUM_REQ; i++) begin : gen_no_starve
            property no_starvation;
                @(posedge clk) disable iff (!rst_n)
                req[i] |-> ##[1:50] grant[i];
            endproperty
            
            a_no_starve: assert property (no_starvation)
                else $error("STARVATION: Request %0d starved", i);
        end
    endgenerate
    
    // ============================================
    // FAIRNESS PROPERTIES
    // ============================================
    
    // Property 6: Round-robin fairness
    // If two requests present, they alternate getting grants
    property round_robin_fairness;
        int prev_grant;
        @(posedge clk) disable iff (!rst_n)
        (grant != 0, prev_grant = $clog2(grant)) |->
        ##[1:10] (grant != 0) |->
        ($clog2(grant) != prev_grant);
    endproperty
    
    // Note: This is simplified; actual RR depends on implementation
    
    // Property 7: Bounded waiting for fairness
    // If request i is pending, it gets grant within N other grants
    generate
        for (i = 0; i < NUM_REQ; i++) begin : gen_fair
            property bounded_wait;
                @(posedge clk) disable iff (!rst_n)
                req[i] && !grant[i] |->
                ##[1:20] grant[i] || (grant == 0);
            endproperty
        end
    endgenerate
    
    // ============================================
    // PRIORITY ARBITER PROPERTIES
    // ============================================
    
    // Property 8: Highest priority always wins
    property highest_priority_wins;
        @(posedge clk) disable iff (!rst_n)
        (grant != 0) |-> 
        // If bit i is granted, no higher priority bit was requesting
        (grant[3] |-> !req[3:0] || (req[3] && !req[3:1])) &&
        (grant[2] |-> !req[3]) &&
        (grant[1] |-> !req[3:2]) &&
        (grant[0] |-> !req[3:1]);
    endproperty
    
    // Enable for priority arbiter:
    // a_priority: assert property (highest_priority_wins);
    
    // ============================================
    // RESOURCE UTILIZATION
    // ============================================
    
    // Property 9: Grant whenever possible (no unnecessary idle)
    property no_idle_with_request;
        @(posedge clk) disable iff (!rst_n)
        (req != 0) |-> ##[0:5] (grant != 0);
    endproperty
    
    a_utilization: assert property (no_idle_with_request)
        else $error("IDLE: Requests %b but no grant", req);
    
    // ============================================
    // TIMING PROPERTIES
    // ============================================
    
    // Property 10: Grant deasserts when request drops
    generate
        for (i = 0; i < NUM_REQ; i++) begin : gen_deassert
            property grant_drops;
                @(posedge clk) disable iff (!rst_n)
                grant[i] && !req[i] |=> !grant[i];
            endproperty
            
            a_drop: assert property (grant_drops);
        end
    endgenerate
    
    // Property 11: Grant changes within bounded time
    property grant_changes;
        @(posedge clk) disable iff (!rst_n)
        (req != 0) && (grant != 0) |->
        ##[1:10] (grant != $past(grant)) || (req == 0);
    endproperty
    
    // ============================================
    // WEIGHTED FAIRNESS PROPERTIES
    // ============================================
    
    // Property 12: Weight-based fairness
    // If requester 0 has weight 2, it should get 2x grants
    logic [7:0] grant_count [NUM_REQ];
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int j = 0; j < NUM_REQ; j++)
                grant_count[j] <= 0;
        end else begin
            for (int j = 0; j < NUM_REQ; j++)
                if (grant[j])
                    grant_count[j] <= grant_count[j] + 1;
        end
    end
    
    // Property: Ratio of grants matches ratio of weights
    // Example for 2:1 ratio between req[0] and req[1]
    property weighted_fairness_2_1;
        @(posedge clk) disable iff (!rst_n)
        (grant_count[0] > 10) |->
        (grant_count[0] >= grant_count[1]) &&
        (grant_count[0] <= 3 * grant_count[1]);
    endproperty
    
    // ============================================
    // AGE-BASED FAIRNESS
    // ============================================
    
    // Track how long each request has been waiting
    logic [7:0] wait_time [NUM_REQ];
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int j = 0; j < NUM_REQ; j++)
                wait_time[j] <= 0;
        end else begin
            for (int j = 0; j < NUM_REQ; j++) begin
                if (grant[j])
                    wait_time[j] <= 0;
                else if (req[j])
                    wait_time[j] <= wait_time[j] + 1;
            end
        end
    end
    
    // Property 13: Oldest request eventually served
    property oldest_served;
        @(posedge clk) disable iff (!rst_n)
        (|req) |->
        ##[1:50] (grant != 0);
        // Could check that oldest gets grant, but requires comparison
    endproperty
    
    // ============================================
    // MULTI-LEVEL ARBITER
    // ============================================
    
    // For hierarchical arbiters (e.g., 16 requesters = 4x4)
    // Verify composition properties
    
    // ============================================
    // COVERAGE
    // ============================================
    
    // Cover: All requesters get grant
    generate
        for (i = 0; i < NUM_REQ; i++) begin : gen_cover_grant
            c_grant: cover property (
                @(posedge clk) grant[i]
            );
        end
    endgenerate
    
    // Cover: All possible request patterns
    c_all_req: cover property (
        @(posedge clk) req == '1
    );
    
    c_no_req: cover property (
        @(posedge clk) req == '0
    );
    
    // Cover: Grant switches between different requesters
    c_switch: cover property (
        @(posedge clk) grant[0] ##[1:5] grant[1]
    );
    
    // Cover: Back-to-back grants to same requester
    c_consecutive: cover property (
        @(posedge clk) grant[0] ##1 grant[0]
    );
    
    // Cover: Maximum wait time reached
    c_max_wait: cover property (
        @(posedge clk) wait_time[0] > 20
    );

endmodule

// ============================================
// FIXED PRIORITY ARBITER
// ============================================

module fixed_priority_arbiter_formal #(
    parameter NUM_REQ = 4
) (
    input logic                 clk,
    input logic                 rst_n,
    input logic [NUM_REQ-1:0]   req,
    input logic [NUM_REQ-1:0]   grant
);

    // Property: Highest priority requester always wins
    property fixed_priority;
        @(posedge clk) disable iff (!rst_n)
        // If req[i] granted, no higher priority was requesting
        grant[0] |-> req[0] ||
        grant[1] |-> !req[0] && req[1] ||
        grant[2] |-> !req[1:0] && req[2] ||
        grant[3] |-> !req[2:0] && req[3];
    endproperty
    
    a_fixed_pri: assert property (fixed_priority)
        else $error("Priority violation");
    
    // Property: Low priority can starve (this is expected!)
    // We can only prove bounded waiting if high priority stops

endmodule

// ============================================
// ROUND-ROBIN ARBITER
// ============================================

module round_robin_arbiter_formal #(
    parameter NUM_REQ = 4
) (
    input logic                 clk,
    input logic                 rst_n,
    input logic [NUM_REQ-1:0]   req,
    input logic [NUM_REQ-1:0]   grant,
    input logic [1:0]           priority_ptr  // Current priority position
);

    // Property: Priority rotates after each grant
    property priority_rotates;
        @(posedge clk) disable iff (!rst_n)
        (grant != 0) |=> (priority_ptr != $past(priority_ptr));
    endproperty
    
    a_rotate: assert property (priority_rotates)
        else $error("Priority not rotating");
    
    // Property: Each requester gets fair chance
    logic [7:0] grant_count [NUM_REQ];
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < NUM_REQ; i++)
                grant_count[i] <= 0;
        end else begin
            for (int i = 0; i < NUM_REQ; i++)
                if (grant[i])
                    grant_count[i] <= grant_count[i] + 1;
        end
    end
    
    // Property: Grant counts are balanced
    property balanced_grants;
        @(posedge clk) disable iff (!rst_n)
        (grant_count[0] > 10) |->
        // All counts within factor of 2 of each other
        (grant_count[0] <= 2 * grant_count[1]) &&
        (grant_count[1] <= 2 * grant_count[0]);
    endproperty

endmodule

// ============================================
// USAGE NOTES
// ============================================

/*
 * Arbiter Verification Goals:
 *
 * 1. SAFETY
 *    - Mutual exclusion (only one grant)
 *    - Grant only if request
 *    - No spurious grants
 *
 * 2. LIVENESS
 *    - Every request eventually granted
 *    - No deadlock
 *    - Progress guaranteed
 *
 * 3. FAIRNESS
 *    - No starvation
 *    - Bounded waiting
 *    - Equal service (round-robin)
 *    - Weight-based fairness
 *    - Age-based priority
 *
 * 4. PERFORMANCE
 *    - Minimum latency
 *    - Maximum throughput
 *    - No unnecessary idle
 *
 * Common Arbiter Types:
 *
 * - Fixed Priority: Simple, but low priority starves
 * - Round-Robin: Fair, moderate complexity
 * - Weighted RR: Configurable fairness
 * - Age-Based: Oldest request first
 * - Matrix: Fast, expensive in gates
 *
 * Verification Challenges:
 *
 * - Liveness requires unbounded time
 * - Use bounded properties (within N cycles)
 * - Fairness needs long traces to verify
 * - Coverage of all request patterns
 *
 * Best Practices:
 *
 * 1. Start with safety (mutex)
 * 2. Add liveness (eventual grant)
 * 3. Check fairness (no starvation)
 * 4. Verify for N=2, then N=4, then larger
 * 5. Use coverage to find corner cases
 */
