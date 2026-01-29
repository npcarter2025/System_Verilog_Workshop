// Liveness Properties Examples
// "Good things eventually happen"
// These properties assert that progress is made and deadlocks don't occur

module liveness_properties_examples #(
    parameter MAX_WAIT = 100  // Maximum cycles to wait
) (
    input logic clk,
    input logic rst_n,
    
    // Request-acknowledge interface
    input logic req,
    input logic ack,
    
    // Arbiter interface
    input logic [3:0] req_vec,
    input logic [3:0] grant_vec,
    
    // State machine interface
    input logic [2:0] state,
    
    // FIFO interface
    input logic push,
    input logic pop,
    input logic full,
    input logic empty,
    input logic almost_full
);

    // Define state encoding for readability
    localparam IDLE   = 3'b000;
    localparam ACTIVE = 3'b001;
    localparam WAIT   = 3'b010;
    localparam DONE   = 3'b011;

    // ============================================
    // REQUEST-ACKNOWLEDGE LIVENESS
    // ============================================
    
    // Property: Request eventually acknowledged (bounded)
    property req_eventually_acked;
        @(posedge clk) disable iff (!rst_n)
        req |-> ##[1:MAX_WAIT] ack;
    endproperty
    
    assert_req_acked: assert property (req_eventually_acked)
        else $error("LIVENESS VIOLATION: Request not acknowledged within %0d cycles", MAX_WAIT);
    
    // Property: Acknowledge eventually deasserted
    property ack_eventually_cleared;
        @(posedge clk) disable iff (!rst_n)
        ack |-> ##[1:20] !ack;
    endproperty
    
    assert_ack_cleared: assert property (ack_eventually_cleared)
        else $error("LIVENESS VIOLATION: Acknowledge stuck high");
    
    // ============================================
    // ARBITER LIVENESS (No Starvation)
    // ============================================
    
    // Property: Each requester eventually gets grant
    // This prevents starvation
    
    property no_starvation_0;
        @(posedge clk) disable iff (!rst_n)
        req_vec[0] |-> ##[1:MAX_WAIT] grant_vec[0];
    endproperty
    
    assert_no_starve_0: assert property (no_starvation_0)
        else $error("LIVENESS VIOLATION: Requester 0 starved");
    
    property no_starvation_1;
        @(posedge clk) disable iff (!rst_n)
        req_vec[1] |-> ##[1:MAX_WAIT] grant_vec[1];
    endproperty
    
    assert_no_starve_1: assert property (no_starvation_1)
        else $error("LIVENESS VIOLATION: Requester 1 starved");
    
    property no_starvation_2;
        @(posedge clk) disable iff (!rst_n)
        req_vec[2] |-> ##[1:MAX_WAIT] grant_vec[2];
    endproperty
    
    assert_no_starve_2: assert property (no_starvation_2)
        else $error("LIVENESS VIOLATION: Requester 2 starved");
    
    property no_starvation_3;
        @(posedge clk) disable iff (!rst_n)
        req_vec[3] |-> ##[1:MAX_WAIT] grant_vec[3];
    endproperty
    
    assert_no_starve_3: assert property (no_starvation_3)
        else $error("LIVENESS VIOLATION: Requester 3 starved");
    
    // ============================================
    // STATE MACHINE LIVENESS
    // ============================================
    
    // Property: State machine makes progress (doesn't get stuck)
    property fsm_makes_progress;
        @(posedge clk) disable iff (!rst_n)
        (state == ACTIVE) |-> ##[1:MAX_WAIT] (state != ACTIVE);
    endproperty
    
    assert_fsm_progress: assert property (fsm_makes_progress)
        else $error("LIVENESS VIOLATION: FSM stuck in ACTIVE state");
    
    // Property: Eventually returns to IDLE
    property eventually_idle;
        @(posedge clk) disable iff (!rst_n)
        (state != IDLE) |-> ##[1:MAX_WAIT] (state == IDLE);
    endproperty
    
    assert_return_idle: assert property (eventually_idle)
        else $error("LIVENESS VIOLATION: FSM never returns to IDLE");
    
    // Property: Can reach DONE state from ACTIVE
    property active_to_done;
        @(posedge clk) disable iff (!rst_n)
        (state == ACTIVE) |-> ##[1:50] (state == DONE);
    endproperty
    
    assert_reach_done: assert property (active_to_done)
        else $error("LIVENESS VIOLATION: Cannot reach DONE from ACTIVE");
    
    // ============================================
    // FIFO LIVENESS
    // ============================================
    
    // Property: Full condition eventually clears
    property full_eventually_clears;
        @(posedge clk) disable iff (!rst_n)
        full && !push |-> ##[1:MAX_WAIT] !full;
    endproperty
    
    assert_full_clears: assert property (full_eventually_clears)
        else $error("LIVENESS VIOLATION: FIFO stuck in full state");
    
    // Property: Empty condition eventually clears (if pushes occur)
    property empty_eventually_clears;
        @(posedge clk) disable iff (!rst_n)
        empty && push |-> ##[1:20] !empty;
    endproperty
    
    assert_empty_clears: assert property (empty_eventually_clears)
        else $error("LIVENESS VIOLATION: FIFO stuck in empty state despite pushes");
    
    // Property: Almost full leads to either full or not almost full
    property almost_full_progress;
        @(posedge clk) disable iff (!rst_n)
        almost_full |-> ##[1:10] (full || !almost_full);
    endproperty
    
    assert_almost_full_progress: assert property (almost_full_progress)
        else $error("LIVENESS VIOLATION: FIFO stuck in almost_full");
    
    // ============================================
    // GENERAL LIVENESS PATTERNS
    // ============================================
    
    // Property: Busy signal eventually deasserts
    logic busy;
    assign busy = (state == ACTIVE) || (state == WAIT);
    
    property busy_eventually_done;
        @(posedge clk) disable iff (!rst_n)
        busy |-> ##[1:MAX_WAIT] !busy;
    endproperty
    
    assert_busy_clears: assert property (busy_eventually_done)
        else $error("LIVENESS VIOLATION: System stuck busy");
    
    // ============================================
    // RESPONSE TIME PROPERTIES
    // ============================================
    
    // Property: Bounded response time for request
    property bounded_response_1_cycle;
        @(posedge clk) disable iff (!rst_n)
        req |-> ##[1:1] ack;
    endproperty
    // Note: This might be too strict, commented as example
    // assert_1cycle_response: assert property (bounded_response_1_cycle);
    
    property bounded_response_5_cycles;
        @(posedge clk) disable iff (!rst_n)
        req |-> ##[1:5] ack;
    endproperty
    
    assert_5cycle_response: assert property (bounded_response_5_cycles)
        else $error("LIVENESS VIOLATION: Response took more than 5 cycles");
    
    // ============================================
    // EVENTUAL CONSISTENCY
    // ============================================
    
    // Property: If conditions are right, operation eventually happens
    property eventually_push_when_not_full;
        @(posedge clk) disable iff (!rst_n)
        !full |-> ##[1:MAX_WAIT] (push || full);
    endproperty
    
    // This assumes environment will eventually push if not full
    // Might be better as an assumption rather than assertion
    // assume property (eventually_push_when_not_full);

endmodule

// ============================================
// HELPER MODULE: Assumptions for Liveness
// ============================================
// Liveness properties often require assumptions about the environment

module liveness_assumptions (
    input logic clk,
    input logic rst_n,
    input logic req,
    input logic ack,
    input logic [3:0] req_vec
);

    // Assume: Request eventually deasserts
    property req_eventually_drops;
        @(posedge clk) disable iff (!rst_n)
        req |-> ##[1:100] !req;
    endproperty
    
    assume_req_drops: assume property (req_eventually_drops);
    
    // Assume: Not all requesters request simultaneously forever
    property not_all_req_forever;
        @(posedge clk) disable iff (!rst_n)
        (req_vec == 4'b1111) |-> ##[1:50] (req_vec != 4'b1111);
    endproperty
    
    assume_req_variety: assume property (not_all_req_forever);
    
    // Assume: Acknowledge leads to request drop
    property ack_causes_req_drop;
        @(posedge clk) disable iff (!rst_n)
        (req && ack) |=> !req;
    endproperty
    
    assume_protocol: assume property (ack_causes_req_drop);

endmodule
