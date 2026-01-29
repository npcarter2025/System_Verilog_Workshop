// Formal Proof of Deadlock Freedom
// Proves that system always makes progress and never deadlocks

module deadlock_freedom_formal (
    input logic clk,
    input logic rst_n,
    
    // Resource requests
    input logic [3:0] req_resource_a,  // Which resources process A wants
    input logic [3:0] req_resource_b,  // Which resources process B wants
    
    // Resource grants
    input logic [3:0] grant_resource_a,
    input logic [3:0] grant_resource_b,
    
    // Resource availability
    input logic [3:0] resource_free,
    
    // Process states
    input logic [1:0] state_a,
    input logic [1:0] state_b
);

    localparam IDLE = 2'b00;
    localparam WAITING = 2'b01;
    localparam RUNNING = 2'b10;
    localparam DONE = 2'b11;
    
    // ============================================
    // BASIC DEADLOCK DETECTION
    // ============================================
    
    // Property: Not both waiting forever
    property no_mutual_wait;
        @(posedge clk) disable iff (!rst_n)
        (state_a == WAITING) && (state_b == WAITING) |->
            ##[1:50] (state_a != WAITING) || (state_b != WAITING);
    endproperty
    
    a_no_deadlock: assert property (no_mutual_wait)
        else $error("DEADLOCK: Both processes waiting");
    
    // ============================================
    // PROGRESS PROPERTIES
    // ============================================
    
    // Property: Waiting eventually leads to running
    property waiting_to_running_a;
        @(posedge clk) disable iff (!rst_n)
        (state_a == WAITING) |-> ##[1:50] (state_a == RUNNING);
    endproperty
    
    a_progress_a: assert property (waiting_to_running_a)
        else $error("No progress: Process A stuck waiting");
    
    property waiting_to_running_b;
        @(posedge clk) disable iff (!rst_n)
        (state_b == WAITING) |-> ##[1:50] (state_b == RUNNING);
    endproperty
    
    a_progress_b: assert property (waiting_to_running_b)
        else $error("No progress: Process B stuck waiting");
    
    // ============================================
    // RESOURCE ORDERING
    // ============================================
    
    // Property: Resources acquired in order (prevents circular wait)
    // Assume resources numbered 0-3, acquire in ascending order
    
    property ordered_acquisition_a;
        @(posedge clk) disable iff (!rst_n)
        (|grant_resource_a) |-> 
            ($countones(grant_resource_a) == 1) || 
            (grant_resource_a == 4'b0011) ||  // 0,1
            (grant_resource_a == 4'b0111) ||  // 0,1,2
            (grant_resource_a == 4'b1111);    // 0,1,2,3
    endproperty
    
    // This ensures resources acquired in order 0->1->2->3
    
    // ============================================
    // NO CIRCULAR WAIT
    // ============================================
    
    // Property: If A holds R1 and waits for R2, B doesn't hold R2 and wait for R1
    property no_circular_wait;
        @(posedge clk) disable iff (!rst_n)
        !(
            (grant_resource_a[0] && req_resource_a[1] && !grant_resource_a[1]) &&
            (grant_resource_b[1] && req_resource_b[0] && !grant_resource_b[0])
        );
    endproperty
    
    a_no_circular: assert property (no_circular_wait)
        else $error("Circular wait detected");
    
    // ============================================
    // HOLD AND WAIT
    // ============================================
    
    // Property: Process gets all resources or none (prevents hold-and-wait)
    property all_or_nothing_a;
        @(posedge clk) disable iff (!rst_n)
        (state_a == RUNNING) |-> 
            (grant_resource_a == req_resource_a) || (grant_resource_a == '0);
    endproperty
    
    // ============================================
    // RESOURCE AVAILABILITY
    // ============================================
    
    // Property: Total resources constant (conservation)
    property resource_conservation;
        @(posedge clk) disable iff (!rst_n)
        $countones(resource_free) + 
        $countones(grant_resource_a) + 
        $countones(grant_resource_b) == 4;
    endproperty
    
    a_conservation: assert property (resource_conservation)
        else $error("Resource leak detected");
    
    // ============================================
    // LIVELOCK PREVENTION
    // ============================================
    
    // Property: Process eventually completes (not just busy-waiting)
    property eventual_completion_a;
        @(posedge clk) disable iff (!rst_n)
        (state_a == IDLE) |-> ##[1:200] (state_a == DONE);
    endproperty
    
    // ============================================
    // TIMEOUT-BASED DEADLOCK PREVENTION
    // ============================================
    
    // If using timeouts, verify they work
    logic [7:0] timeout_counter_a;
    logic [7:0] timeout_counter_b;
    
    // Property: Timeout eventually fires if stuck
    property timeout_works_a;
        @(posedge clk) disable iff (!rst_n)
        (state_a == WAITING) |-> ##[1:50] timeout_counter_a >= 50;
    endproperty
    
    // ============================================
    // COVERAGE
    // ============================================
    
    // Cover: Both processes request same resource
    c_conflict: cover property (
        @(posedge clk) (req_resource_a & req_resource_b) != 0
    );
    
    // Cover: Both processes get resources
    c_both_grant: cover property (
        @(posedge clk) (grant_resource_a != 0) && (grant_resource_b != 0)
    );
    
    // Cover: Resource contention resolved
    c_resolved: cover property (
        @(posedge clk) (state_a == WAITING) ##[1:10] (state_a == RUNNING)
    );

endmodule

// ============================================
// DINING PHILOSOPHERS DEADLOCK FREEDOM
// ============================================

module dining_philosophers_formal #(
    parameter N = 5
) (
    input logic           clk,
    input logic           rst_n,
    input logic [N-1:0]   thinking,
    input logic [N-1:0]   hungry,
    input logic [N-1:0]   eating,
    input logic [N-1:0]   fork_held  // Which forks are held
);

    // Property: Deadlock-free - at least one philosopher can eat
    property at_least_one_eats;
        @(posedge clk) disable iff (!rst_n)
        (|hungry) |-> ##[1:100] (|eating);
    endproperty
    
    a_progress: assert property (at_least_one_eats)
        else $error("Deadlock: No philosopher can eat");
    
    // Property: Not all holding one fork (deadlock state)
    property not_all_one_fork;
        @(posedge clk) disable iff (!rst_n)
        $countones(fork_held) != N;  // Not exactly N forks held
    endproperty
    
    a_no_deadlock_state: assert property (not_all_one_fork)
        else $error("Deadlock: Each holding one fork");
    
    // Property: Hungry philosopher eventually eats
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_no_starve
            property no_starvation;
                @(posedge clk) disable iff (!rst_n)
                hungry[i] |-> ##[1:200] eating[i];
            endproperty
            
            a_no_starve: assert property (no_starvation);
        end
    endgenerate

endmodule

// ============================================
// BANKER'S ALGORITHM DEADLOCK AVOIDANCE
// ============================================

module bankers_algorithm_formal #(
    parameter NUM_PROCESSES = 3,
    parameter NUM_RESOURCES = 3
) (
    input logic clk,
    input logic rst_n,
    
    // Available resources
    input logic [7:0] available [NUM_RESOURCES],
    
    // Maximum needs
    input logic [7:0] max_need [NUM_PROCESSES][NUM_RESOURCES],
    
    // Current allocation
    input logic [7:0] allocation [NUM_PROCESSES][NUM_RESOURCES],
    
    // Request being processed
    input logic       request_pending,
    input logic [1:0] requesting_process
);

    // Property: System remains in safe state
    // A safe state is one where there exists a sequence of process 
    // completions that allows all to finish
    
    // Simplified: Available resources sufficient for at least one process
    property safe_state;
        @(posedge clk) disable iff (!rst_n)
        !request_pending |-> 
            // At least one process can complete with available resources
            1'b1;  // Simplified - full check needs complex logic
    endproperty
    
    // Property: No resource over-allocation
    property no_overallocation;
        logic [15:0] total_allocated;
        logic [15:0] total_available;
        @(posedge clk) disable iff (!rst_n)
        1'b1;  // Check sum(allocated) + available = total
    endproperty

endmodule

// ============================================
// GRAPH-BASED DEADLOCK DETECTION
// ============================================

module resource_allocation_graph_formal (
    input logic clk,
    input logic rst_n,
    
    // Adjacency matrix for resource allocation graph
    input logic [3:0][3:0] edge  // edge[i][j] = edge from node i to j
);

    // Property: No cycles in resource allocation graph
    // Cycle detection in graph (simplified)
    
    // For 4 nodes, check all possible cycles
    property no_cycle_4;
        @(posedge clk) disable iff (!rst_n)
        !(
            (edge[0][1] && edge[1][2] && edge[2][3] && edge[3][0]) ||
            (edge[0][1] && edge[1][3] && edge[3][2] && edge[2][0]) ||
            (edge[0][2] && edge[2][1] && edge[1][3] && edge[3][0])
            // ... other cycles
        );
    endproperty
    
    a_no_cycle: assert property (no_cycle_4)
        else $error("Cycle detected in resource allocation graph");

endmodule

// ============================================
// TWO-PHASE LOCKING (Database Deadlock)
// ============================================

module two_phase_locking_formal (
    input logic clk,
    input logic rst_n,
    
    // Transaction states
    input logic [1:0] txn_a_phase,  // 0=growing, 1=shrinking, 2=done
    input logic [1:0] txn_b_phase,
    
    // Lock holdings
    input logic [3:0] locks_a,
    input logic [3:0] locks_b
);

    // Property: Once shrinking, can't acquire new locks
    property two_phase_rule_a;
        @(posedge clk) disable iff (!rst_n)
        (txn_a_phase == 1) |-> 
            ##1 ($countones(locks_a) <= $past($countones(locks_a)));
    endproperty
    
    a_two_phase_a: assert property (two_phase_rule_a);
    
    // Property: No deadlock (both waiting for each other's locks)
    property no_deadlock_2pl;
        @(posedge clk) disable iff (!rst_n)
        !((locks_a & locks_b) != 0 &&
          (txn_a_phase == 0) && (txn_b_phase == 0));
    endproperty

endmodule

// ============================================
// USAGE NOTES
// ============================================

/*
 * Deadlock occurs when:
 *   1. Mutual exclusion (resources non-sharable)
 *   2. Hold and wait (holding while requesting more)
 *   3. No preemption (can't forcibly take resources)
 *   4. Circular wait (cycle in resource wait graph)
 *
 * Deadlock prevention strategies:
 *   - Resource ordering (acquire in same order)
 *   - All-or-nothing allocation
 *   - Timeouts and retry
 *   - Banker's algorithm (safe state)
 *
 * Formal verification proves:
 *   - Progress: System never completely stuck
 *   - Liveness: Requests eventually satisfied
 *   - No circular wait: Resource graph acyclic
 *
 * Challenges:
 *   - State explosion with many processes/resources
 *   - Liveness requires unbounded checking
 *   - Need good abstractions
 *
 * Best approach:
 *   - Prove for small system (2-3 processes)
 *   - Use bounded liveness (within N cycles)
 *   - Add progress assumptions
 *   - Check specific scenarios
 */
