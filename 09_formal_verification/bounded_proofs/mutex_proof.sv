// Formal Proof of Mutual Exclusion
// Proves that two (or more) processes never execute critical section simultaneously

module mutex_formal_proof (
    input logic clk,
    input logic rst_n,
    
    // Process A
    input logic req_a,
    input logic grant_a,
    input logic in_critical_a,
    
    // Process B
    input logic req_b,
    input logic grant_b,
    input logic in_critical_b
);

    // ============================================
    // CORE MUTEX PROPERTY
    // ============================================
    
    // Property: Mutual exclusion - never both in critical section
    property mutex;
        @(posedge clk) disable iff (!rst_n)
        !(in_critical_a && in_critical_b);
    endproperty
    
    a_mutex: assert property (mutex)
        else $error("MUTEX VIOLATION: Both processes in critical section!");
    
    // ============================================
    // GRANT MUTUAL EXCLUSION
    // ============================================
    
    // Property: At most one grant at a time
    property grant_mutex;
        @(posedge clk) disable iff (!rst_n)
        !(grant_a && grant_b);
    endproperty
    
    a_grant_mutex: assert property (grant_mutex)
        else $error("GRANT VIOLATION: Both grants active");
    
    // ============================================
    // GRANT IMPLIES CRITICAL SECTION
    // ============================================
    
    // Property: Can only enter critical section with grant
    property enter_with_grant_a;
        @(posedge clk) disable iff (!rst_n)
        $rose(in_critical_a) |-> grant_a;
    endproperty
    
    a_grant_req_a: assert property (enter_with_grant_a)
        else $error("Process A entered critical section without grant");
    
    property enter_with_grant_b;
        @(posedge clk) disable iff (!rst_n)
        $rose(in_critical_b) |-> grant_b;
    endproperty
    
    a_grant_req_b: assert property (enter_with_grant_b)
        else $error("Process B entered critical section without grant");
    
    // ============================================
    // LIVENESS PROPERTIES
    // ============================================
    
    // Property: Request eventually granted
    property eventual_grant_a;
        @(posedge clk) disable iff (!rst_n)
        req_a |-> ##[1:50] grant_a;
    endproperty
    
    a_liveness_a: assert property (eventual_grant_a)
        else $error("Liveness violation: Process A starved");
    
    property eventual_grant_b;
        @(posedge clk) disable iff (!rst_n)
        req_b |-> ##[1:50] grant_b;
    endproperty
    
    a_liveness_b: assert property (eventual_grant_b)
        else $error("Liveness violation: Process B starved");
    
    // ============================================
    // CRITICAL SECTION DURATION
    // ============================================
    
    // Property: Critical section eventually exits
    property exit_critical_a;
        @(posedge clk) disable iff (!rst_n)
        in_critical_a |-> ##[1:100] !in_critical_a;
    endproperty
    
    a_exit_a: assert property (exit_critical_a)
        else $error("Process A stuck in critical section");
    
    property exit_critical_b;
        @(posedge clk) disable iff (!rst_n)
        in_critical_b |-> ##[1:100] !in_critical_b;
    endproperty
    
    a_exit_b: assert property (exit_critical_b)
        else $error("Process B stuck in critical section");
    
    // ============================================
    // COVERAGE
    // ============================================
    
    // Cover: Process A enters critical section
    c_enter_a: cover property (
        @(posedge clk) $rose(in_critical_a)
    );
    
    // Cover: Process B enters critical section
    c_enter_b: cover property (
        @(posedge clk) $rose(in_critical_b)
    );
    
    // Cover: Alternating access
    c_alternate: cover property (
        @(posedge clk) in_critical_a ##[1:$] !in_critical_a ##[1:$] in_critical_b
    );
    
    // Cover: Both request simultaneously
    c_both_req: cover property (
        @(posedge clk) req_a && req_b
    );

endmodule

// ============================================
// PETERSON'S ALGORITHM MUTEX
// ============================================

module peterson_mutex_formal (
    input logic clk,
    input logic rst_n,
    
    // Shared variables
    input logic flag_a,       // Process A wants to enter
    input logic flag_b,       // Process B wants to enter
    input logic turn,         // Whose turn (0=A, 1=B)
    
    // Process states
    input logic in_critical_a,
    input logic in_critical_b
);

    // Property: Peterson's mutex guarantee
    property peterson_mutex;
        @(posedge clk) disable iff (!rst_n)
        !(in_critical_a && in_critical_b);
    endproperty
    
    a_peterson: assert property (peterson_mutex);
    
    // Property: Entry condition for process A
    // A enters when: flag_a && (!flag_b || turn==0)
    property entry_condition_a;
        @(posedge clk) disable iff (!rst_n)
        $rose(in_critical_a) |-> 
            flag_a && (!flag_b || (turn == 1'b0));
    endproperty
    
    // Property: Entry condition for process B
    property entry_condition_b;
        @(posedge clk) disable iff (!rst_n)
        $rose(in_critical_b) |-> 
            flag_b && (!flag_a || (turn == 1'b1));
    endproperty

endmodule

// ============================================
// SEMAPHORE-BASED MUTEX
// ============================================

module semaphore_mutex_formal (
    input logic        clk,
    input logic        rst_n,
    input logic [7:0]  semaphore,  // 1=available, 0=taken
    input logic        in_critical_a,
    input logic        in_critical_b
);

    // Property: Semaphore is binary (0 or 1)
    property binary_semaphore;
        @(posedge clk) disable iff (!rst_n)
        semaphore <= 1;
    endproperty
    
    a_binary: assert property (binary_semaphore);
    
    // Property: Mutex via semaphore
    property semaphore_mutex;
        @(posedge clk) disable iff (!rst_n)
        (in_critical_a || in_critical_b) |-> (semaphore == 0);
    endproperty
    
    a_sem_mutex: assert property (semaphore_mutex);
    
    // Property: Can't both be in critical section
    property mutex_guarantee;
        @(posedge clk) disable iff (!rst_n)
        !(in_critical_a && in_critical_b);
    endproperty
    
    a_mutex_sem: assert property (mutex_guarantee);

endmodule

// ============================================
// TEST-AND-SET MUTEX
// ============================================

module test_and_set_mutex_formal (
    input logic clk,
    input logic rst_n,
    input logic lock,           // 0=free, 1=locked
    input logic in_critical_a,
    input logic in_critical_b
);

    // Property: Lock indicates critical section occupancy
    property lock_indicates_occupancy;
        @(posedge clk) disable iff (!rst_n)
        (in_critical_a || in_critical_b) |-> lock;
    endproperty
    
    a_lock_occ: assert property (lock_indicates_occupancy);
    
    // Property: Mutual exclusion
    property tas_mutex;
        @(posedge clk) disable iff (!rst_n)
        !(in_critical_a && in_critical_b);
    endproperty
    
    a_tas_mutex: assert property (tas_mutex);
    
    // Property: Lock released after critical section
    property lock_released;
        @(posedge clk) disable iff (!rst_n)
        $fell(in_critical_a) || $fell(in_critical_b) |=> !lock;
    endproperty

endmodule

// ============================================
// N-PROCESS MUTEX
// ============================================

module n_process_mutex_formal #(
    parameter N = 4
) (
    input logic           clk,
    input logic           rst_n,
    input logic [N-1:0]   in_critical
);

    // Property: At most one process in critical section
    property n_mutex;
        @(posedge clk) disable iff (!rst_n)
        $onehot0(in_critical);
    endproperty
    
    a_n_mutex: assert property (n_mutex)
        else $error("N-MUTEX VIOLATION: %b in critical", in_critical);
    
    // Property: No process stays forever
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_exit
            property exit_critical;
                @(posedge clk) disable iff (!rst_n)
                in_critical[i] |-> ##[1:100] !in_critical[i];
            endproperty
            
            a_exit: assert property (exit_critical);
        end
    endgenerate
    
    // Cover: Each process enters
    generate
        for (i = 0; i < N; i++) begin : gen_cover
            c_enter: cover property (
                @(posedge clk) in_critical[i]
            );
        end
    endgenerate

endmodule

// ============================================
// MUTEX WITH PRIORITY
// ============================================

module priority_mutex_formal (
    input logic clk,
    input logic rst_n,
    
    // High priority process
    input logic req_high,
    input logic grant_high,
    input logic in_critical_high,
    
    // Low priority process
    input logic req_low,
    input logic grant_low,
    input logic in_critical_low
);

    // Property: Basic mutex
    property mutex;
        @(posedge clk) disable iff (!rst_n)
        !(in_critical_high && in_critical_low);
    endproperty
    
    a_mutex: assert property (mutex);
    
    // Property: High priority gets preference
    property high_priority_preference;
        @(posedge clk) disable iff (!rst_n)
        req_high && req_low |-> 
            ##[1:$] grant_high before grant_low;
    endproperty
    
    // Property: Low priority not starved (bounded waiting)
    property no_starvation_low;
        @(posedge clk) disable iff (!rst_n)
        req_low |-> ##[1:100] grant_low;
    endproperty
    
    a_no_starve: assert property (no_starvation_low)
        else $error("Low priority process starved");

endmodule

// ============================================
// READER-WRITER MUTEX
// ============================================

module reader_writer_mutex_formal #(
    parameter NUM_READERS = 4
) (
    input logic                 clk,
    input logic                 rst_n,
    input logic [NUM_READERS-1:0] reading,
    input logic                 writing
);

    // Property: No writer while readers active
    property no_write_during_read;
        @(posedge clk) disable iff (!rst_n)
        (|reading) |-> !writing;
    endproperty
    
    a_no_write: assert property (no_write_during_read)
        else $error("Writer active while readers present");
    
    // Property: No readers while writer active
    property no_read_during_write;
        @(posedge clk) disable iff (!rst_n)
        writing |-> (reading == '0);
    endproperty
    
    a_no_read: assert property (no_read_during_write)
        else $error("Readers active while writer present");
    
    // Property: Multiple readers allowed
    property multiple_readers_ok;
        @(posedge clk) disable iff (!rst_n)
        !writing;  // Multiple readers OK when no writer
    endproperty
    
    // Cover: Multiple readers
    c_multi_read: cover property (
        @(posedge clk) $countones(reading) > 1
    );

endmodule

// ============================================
// USAGE NOTES
// ============================================

/*
 * Mutex (Mutual Exclusion) ensures:
 *   1. Only one process in critical section at a time
 *   2. Eventually every requester gets access (no starvation)
 *   3. Progress is made (no deadlock)
 *
 * Formal verification proves:
 *   - Safety: Never both in critical section
 *   - Liveness: Requests eventually granted
 *   - Fairness: No starvation
 *
 * Common mutex algorithms:
 *   - Peterson's algorithm (2 processes)
 *   - Dekker's algorithm (2 processes)
 *   - Lamport's bakery algorithm (N processes)
 *   - Hardware: Test-and-set, Compare-and-swap
 *   - OS: Semaphores, monitors
 *
 * Formal challenges:
 *   - Unbounded liveness (use bounded version)
 *   - Fairness assumptions needed
 *   - State explosion for many processes
 *
 * Best practices:
 *   - Prove for 2 processes first
 *   - Extend to N with induction
 *   - Add assumptions about progress
 */
