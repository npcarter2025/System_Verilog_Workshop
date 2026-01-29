// Fairness Properties Examples
// Ensure fair scheduling and no starvation with bounded waiting

module fairness_properties_examples #(
    parameter NUM_REQUESTERS = 4,
    parameter MAX_UNFAIRNESS = 10  // Max times others can be granted before this one
) (
    input logic clk,
    input logic rst_n,
    
    // Arbiter interface
    input logic [NUM_REQUESTERS-1:0] req,
    input logic [NUM_REQUESTERS-1:0] grant
);

    // ============================================
    // ROUND-ROBIN FAIRNESS
    // ============================================
    
    // Property: Bounded overtaking - no requester is skipped too many times
    // If req[i] is continuously asserted, it gets grant within N grants to others
    
    // Helper: Count grants to others while req[i] is active
    logic [7:0] skip_count [NUM_REQUESTERS];
    
    genvar i;
    generate
        for (i = 0; i < NUM_REQUESTERS; i++) begin : gen_fairness
            
            // Count how many times others are granted while this req is waiting
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n)
                    skip_count[i] <= 0;
                else if (grant[i])
                    skip_count[i] <= 0;  // Reset when granted
                else if (req[i] && (|grant) && !grant[i])
                    skip_count[i] <= skip_count[i] + 1;  // Increment when others granted
            end
            
            // Property: Skip count doesn't exceed maximum
            property bounded_unfairness;
                @(posedge clk) disable iff (!rst_n)
                req[i] |-> skip_count[i] <= MAX_UNFAIRNESS;
            endproperty
            
            assert_fair: assert property (bounded_unfairness)
                else $error("FAIRNESS VIOLATION: Requester %0d skipped %0d times", 
                           i, skip_count[i]);
        end
    endgenerate
    
    // ============================================
    // STRICT FAIRNESS
    // ============================================
    
    // Property: If all request, each gets turn within NUM_REQUESTERS grants
    property all_get_turn;
        @(posedge clk) disable iff (!rst_n)
        (req == '1) |-> (
            ##[0:NUM_REQUESTERS] grant[0] and
            ##[0:NUM_REQUESTERS] grant[1] and
            ##[0:NUM_REQUESTERS] grant[2] and
            ##[0:NUM_REQUESTERS] grant[3]
        );
    endproperty
    
    assert_all_turn: assert property (all_get_turn)
        else $error("FAIRNESS VIOLATION: Not all requesters served within window");
    
    // ============================================
    // PROPORTIONAL FAIRNESS
    // ============================================
    
    // Track grants per requester
    logic [15:0] grant_count [NUM_REQUESTERS];
    
    generate
        for (i = 0; i < NUM_REQUESTERS; i++) begin : gen_count
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n)
                    grant_count[i] <= 0;
                else if (grant[i])
                    grant_count[i] <= grant_count[i] + 1;
            end
        end
    endgenerate
    
    // Property: Grant counts don't diverge too much (within 2x)
    // This ensures proportional fairness over time
    property proportional_grants;
        @(posedge clk) disable iff (!rst_n)
        (grant_count[0] > 10) |-> (
            (grant_count[1] * 2 >= grant_count[0]) &&
            (grant_count[2] * 2 >= grant_count[0]) &&
            (grant_count[3] * 2 >= grant_count[0])
        );
    endproperty
    
    // Note: This assumes all requesters are equally active
    // In practice, you'd normalize by request counts
    
    // ============================================
    // PRIORITY FAIRNESS
    // ============================================
    
    // Property: Higher priority eventually served first
    // Assume req[3] is highest priority, req[0] is lowest
    
    property high_priority_served_first;
        @(posedge clk) disable iff (!rst_n)
        (req[3] && req[0]) |-> (
            grant[3] || ##[1:$] (grant[3] ##0 !grant[0])
        );
    endproperty
    
    // This ensures if both request, high priority gets it first
    // or at least not after low priority
    
    // ============================================
    // WEIGHTED FAIRNESS
    // ============================================
    
    // Property: Requester with weight W gets approximately W times more grants
    // Example: req[3] has weight 2, req[0] has weight 1
    
    property weighted_fairness_2_to_1;
        @(posedge clk) disable iff (!rst_n)
        (grant_count[3] > 20) |-> (
            grant_count[3] >= grant_count[0] &&
            grant_count[3] <= (grant_count[0] * 3)  // Within 3x (allowing variance)
        );
    endproperty
    
    // ============================================
    // AGE-BASED FAIRNESS
    // ============================================
    
    // Track how long each request has been waiting
    logic [7:0] wait_time [NUM_REQUESTERS];
    
    generate
        for (i = 0; i < NUM_REQUESTERS; i++) begin : gen_wait_time
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n)
                    wait_time[i] <= 0;
                else if (grant[i])
                    wait_time[i] <= 0;
                else if (req[i])
                    wait_time[i] <= wait_time[i] + 1;
                else
                    wait_time[i] <= 0;
            end
        end
    endgenerate
    
    // Property: Oldest request eventually served
    logic [1:0] oldest_req;
    always_comb begin
        oldest_req = 0;
        if (wait_time[1] > wait_time[oldest_req]) oldest_req = 1;
        if (wait_time[2] > wait_time[oldest_req]) oldest_req = 2;
        if (wait_time[3] > wait_time[oldest_req]) oldest_req = 3;
    end
    
    property oldest_served_first;
        @(posedge clk) disable iff (!rst_n)
        (|req) && (wait_time[oldest_req] > 5) |-> 
            ##[1:5] grant[oldest_req];
    endproperty
    
    assert_oldest_first: assert property (oldest_served_first)
        else $error("FAIRNESS VIOLATION: Oldest request not served");
    
    // ============================================
    // CYCLIC FAIRNESS (Lottery Scheduling)
    // ============================================
    
    // Property: Over a window of N grants, each requester gets ~equal grants
    localparam WINDOW_SIZE = 16;
    logic [3:0] window_grants [NUM_REQUESTERS];
    logic [4:0] window_count;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int j = 0; j < NUM_REQUESTERS; j++)
                window_grants[j] <= 0;
            window_count <= 0;
        end else if (|grant) begin
            if (window_count == WINDOW_SIZE - 1) begin
                // Reset window
                for (int j = 0; j < NUM_REQUESTERS; j++)
                    window_grants[j] <= grant[j];
                window_count <= 0;
            end else begin
                for (int j = 0; j < NUM_REQUESTERS; j++)
                    if (grant[j])
                        window_grants[j] <= window_grants[j] + 1;
                window_count <= window_count + 1;
            end
        end
    end
    
    // Property: Within each window, grant counts are balanced
    property window_fairness;
        @(posedge clk) disable iff (!rst_n)
        (window_count == WINDOW_SIZE - 1) |-> (
            (window_grants[0] <= window_grants[1] + 2) &&
            (window_grants[1] <= window_grants[0] + 2) &&
            (window_grants[2] <= window_grants[3] + 2) &&
            (window_grants[3] <= window_grants[2] + 2)
        );
    endproperty
    
    // ============================================
    // STARVATION FREEDOM WITH TIMEOUT
    // ============================================
    
    // Property: No request waits longer than MAX_WAIT cycles
    generate
        for (i = 0; i < NUM_REQUESTERS; i++) begin : gen_timeout
            property no_timeout;
                @(posedge clk) disable iff (!rst_n)
                wait_time[i] < (MAX_UNFAIRNESS * 2);
            endproperty
            
            assert_no_timeout: assert property (no_timeout)
                else $error("FAIRNESS VIOLATION: Requester %0d timed out after %0d cycles",
                           i, wait_time[i]);
        end
    endgenerate
    
    // ============================================
    // FAIR QUEUEING
    // ============================================
    
    // Property: Requests are served in the order received (FIFO fairness)
    // This is complex and typically requires tracking request order
    
    // Simplified: If req[i] arrives before req[j], req[i] served first
    logic [NUM_REQUESTERS-1:0] req_prev;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            req_prev <= 0;
        else
            req_prev <= req;
    end
    
    // New request detection
    logic [NUM_REQUESTERS-1:0] new_req;
    assign new_req = req & ~req_prev;
    
    // If req[0] arrives and later req[1] arrives, req[0] should be served first
    property fifo_order_0_1;
        @(posedge clk) disable iff (!rst_n)
        (new_req[0] ##[1:$] new_req[1]) |->
            (!grant[1] throughout (##[0:MAX_UNFAIRNESS] grant[0]));
    endproperty
    
    // This ensures req[1] doesn't get granted before req[0] if req[0] came first

endmodule

// ============================================
// FORMAL VERIFICATION TIPS FOR FAIRNESS
// ============================================
/*
 * 1. Fairness often requires assumptions about the environment:
 *    - Assume requests eventually deassert
 *    - Assume bounded arrival rates
 *    - Assume system isn't overloaded
 *
 * 2. Use bounded properties for tractability:
 *    - Instead of "eventually", use "within N cycles"
 *    - Set N based on expected system behavior
 *
 * 3. Statistical fairness may need auxiliary code:
 *    - Counters to track grants over time
 *    - Windows for measuring fairness
 *
 * 4. Consider different fairness metrics:
 *    - Temporal: bounded waiting time
 *    - Proportional: equal share of grants
 *    - Priority-aware: weighted fairness
 *    - Age-based: oldest first
 */
