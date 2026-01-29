// Compositional Formal Verification using Assume-Guarantee Reasoning
// Verifies system by proving components independently, then composing results

module compositional_proof_example (
    input logic        clk,
    input logic        rst_n,
    
    // System inputs
    input logic [31:0] system_in,
    input logic        system_valid_in,
    
    // Module A interface
    input logic [31:0] a_in,
    input logic        a_valid_in,
    input logic [31:0] a_out,
    input logic        a_valid_out,
    
    // Module B interface
    input logic [31:0] b_in,
    input logic        b_valid_in,
    input logic [31:0] b_out,
    input logic        b_valid_out,
    
    // Module C interface
    input logic [31:0] c_in,
    input logic        c_valid_in,
    input logic [31:0] c_out,
    input logic        c_valid_out,
    
    // System output
    input logic [31:0] system_out,
    input logic        system_valid_out
);

    // ============================================
    // COMPOSITIONAL REASONING PATTERN
    // ============================================
    
    /*
     * System: A → B → C
     * 
     * Step 1: Verify A in isolation
     *   - Assume: valid inputs
     *   - Prove: output properties
     *
     * Step 2: Verify B in isolation
     *   - Assume: A's output properties (from Step 1)
     *   - Prove: B's output properties
     *
     * Step 3: Verify C in isolation
     *   - Assume: B's output properties (from Step 2)
     *   - Prove: C's output properties
     *
     * Step 4: Compose results
     *   - If A's guarantees match B's assumptions
     *   - And B's guarantees match C's assumptions
     *   - Then system property holds end-to-end
     */
    
    // ============================================
    // MODULE A: VERIFICATION IN ISOLATION
    // ============================================
    
    // Module A Assumptions (about its environment)
    assume property (@(posedge clk) disable iff (!rst_n)
        a_valid_in |-> !$isunknown(a_in)
    );
    
    assume property (@(posedge clk) disable iff (!rst_n)
        a_valid_in && !a_valid_out |=> a_valid_in
    );
    
    // Module A Guarantees (what it promises)
    assert property (@(posedge clk) disable iff (!rst_n)
        a_valid_out |-> !$isunknown(a_out)
    ) else $error("Module A: output undefined");
    
    assert property (@(posedge clk) disable iff (!rst_n)
        a_valid_in |-> ##[1:10] a_valid_out
    ) else $error("Module A: response timeout");
    
    // Module A Functional Property
    property module_a_function;
        logic [31:0] in_val;
        @(posedge clk) disable iff (!rst_n)
        (a_valid_in, in_val = a_in) |->
        ##[1:10] (a_valid_out && (a_out == in_val + 100));
    endproperty
    
    assert property (module_a_function)
        else $error("Module A: incorrect function");
    
    // ============================================
    // MODULE B: VERIFICATION IN ISOLATION
    // ============================================
    
    // Module B Assumptions (inherited from A's guarantees!)
    assume property (@(posedge clk) disable iff (!rst_n)
        b_valid_in |-> !$isunknown(b_in)
    );
    
    assume property (@(posedge clk) disable iff (!rst_n)
        b_valid_in |-> ##[1:10] b_valid_out
    );
    
    // Module B Guarantees
    assert property (@(posedge clk) disable iff (!rst_n)
        b_valid_out |-> !$isunknown(b_out)
    ) else $error("Module B: output undefined");
    
    // Module B Functional Property
    property module_b_function;
        logic [31:0] in_val;
        @(posedge clk) disable iff (!rst_n)
        (b_valid_in, in_val = b_in) |->
        ##[1:5] (b_valid_out && (b_out == in_val * 2));
    endproperty
    
    assert property (module_b_function)
        else $error("Module B: incorrect function");
    
    // ============================================
    // MODULE C: VERIFICATION IN ISOLATION
    // ============================================
    
    // Module C Assumptions
    assume property (@(posedge clk) disable iff (!rst_n)
        c_valid_in |-> !$isunknown(c_in)
    );
    
    // Module C Guarantees
    assert property (@(posedge clk) disable iff (!rst_n)
        c_valid_out |-> !$isunknown(c_out)
    ) else $error("Module C: output undefined");
    
    // Module C Functional Property
    property module_c_function;
        logic [31:0] in_val;
        @(posedge clk) disable iff (!rst_n)
        (c_valid_in, in_val = c_in) |->
        ##[1:3] (c_valid_out && (c_out == in_val - 50));
    endproperty
    
    assert property (module_c_function)
        else $error("Module C: incorrect function");
    
    // ============================================
    // COMPOSITION: SYSTEM-LEVEL PROPERTY
    // ============================================
    
    // If A, B, C each satisfy their contracts,
    // then the composed system satisfies end-to-end property
    
    // System Property: out = (in + 100) * 2 - 50
    property system_end_to_end;
        logic [31:0] in_val;
        logic [31:0] expected;
        @(posedge clk) disable iff (!rst_n)
        (system_valid_in, 
         in_val = system_in,
         expected = (in_val + 100) * 2 - 50) |->
        ##[1:50] (system_valid_out && (system_out == expected));
    endproperty
    
    assert property (system_end_to_end)
        else $error("System: end-to-end property failed");
    
    // ============================================
    // INTERFACE CONSISTENCY CHECKS
    // ============================================
    
    // Verify A's output connects to B's input
    property a_to_b_connection;
        @(posedge clk) disable iff (!rst_n)
        a_valid_out |=> (b_valid_in && (b_in == $past(a_out)));
    endproperty
    
    assert property (a_to_b_connection)
        else $error("Connection A→B broken");
    
    // Verify B's output connects to C's input
    property b_to_c_connection;
        @(posedge clk) disable iff (!rst_n)
        b_valid_out |=> (c_valid_in && (c_in == $past(b_out)));
    endproperty
    
    assert property (b_to_c_connection)
        else $error("Connection B→C broken");

endmodule

// ============================================
// PARALLEL COMPOSITION
// ============================================

module parallel_compositional_proof (
    input logic        clk,
    input logic        rst_n,
    
    // Parallel modules (both process same input)
    input logic [31:0] input_data,
    input logic        input_valid,
    
    // Module P
    input logic [31:0] p_out,
    input logic        p_valid,
    
    // Module Q
    input logic [31:0] q_out,
    input logic        q_valid,
    
    // Combiner
    input logic [31:0] combined_out,
    input logic        combined_valid
);

    // ============================================
    // MODULE P CONTRACT
    // ============================================
    
    assume property (@(posedge clk) disable iff (!rst_n)
        input_valid |-> !$isunknown(input_data)
    );
    
    assert property (@(posedge clk) disable iff (!rst_n)
        input_valid |-> ##[1:10] p_valid
    );
    
    // ============================================
    // MODULE Q CONTRACT
    // ============================================
    
    assume property (@(posedge clk) disable iff (!rst_n)
        input_valid |-> !$isunknown(input_data)
    );
    
    assert property (@(posedge clk) disable iff (!rst_n)
        input_valid |-> ##[1:10] q_valid
    );
    
    // ============================================
    // PARALLEL COMPOSITION PROPERTY
    // ============================================
    
    // Both modules respond
    property both_respond;
        @(posedge clk) disable iff (!rst_n)
        input_valid |-> ##[1:20] (p_valid && q_valid);
    endproperty
    
    assert property (both_respond);
    
    // Results combined correctly
    property combination_correct;
        @(posedge clk) disable iff (!rst_n)
        (p_valid && q_valid) |->
        ##[1:5] (combined_valid && (combined_out == p_out + q_out));
    endproperty
    
    assert property (combination_correct);

endmodule

// ============================================
// HIERARCHICAL COMPOSITION
// ============================================

module hierarchical_compositional_proof (
    input logic        clk,
    input logic        rst_n,
    
    // Top level
    input logic        top_req,
    input logic        top_ack,
    
    // Subsystem 1
    input logic        sub1_req,
    input logic        sub1_ack,
    
    // Subsystem 1 → Module A
    input logic        mod_a_req,
    input logic        mod_a_ack,
    
    // Subsystem 1 → Module B
    input logic        mod_b_req,
    input logic        mod_b_ack
);

    // ============================================
    // LEAF MODULE A
    // ============================================
    
    assume property (@(posedge clk) disable iff (!rst_n)
        mod_a_req |-> ##[1:10] mod_a_ack
    );
    
    assert property (@(posedge clk) disable iff (!rst_n)
        mod_a_req |-> ##[1:5] mod_a_ack
    );
    
    // ============================================
    // LEAF MODULE B
    // ============================================
    
    assume property (@(posedge clk) disable iff (!rst_n)
        mod_b_req |-> ##[1:10] mod_b_ack
    );
    
    assert property (@(posedge clk) disable iff (!rst_n)
        mod_b_req |-> ##[1:7] mod_b_ack
    );
    
    // ============================================
    // SUBSYSTEM 1 (composed of A and B)
    // ============================================
    
    // Subsystem assumes its environment behaves
    assume property (@(posedge clk) disable iff (!rst_n)
        sub1_req |-> ##[1:20] sub1_ack
    );
    
    // Subsystem guarantees (based on A and B)
    // Max latency = max(A, B) + overhead
    assert property (@(posedge clk) disable iff (!rst_n)
        sub1_req |-> ##[1:15] sub1_ack
    );
    
    // ============================================
    // TOP LEVEL (composed of subsystems)
    // ============================================
    
    assert property (@(posedge clk) disable iff (!rst_n)
        top_req |-> ##[1:30] top_ack
    );

endmodule

// ============================================
// FEEDBACK COMPOSITION
// ============================================

module feedback_compositional_proof (
    input logic        clk,
    input logic        rst_n,
    
    // Forward path
    input logic [31:0] fwd_in,
    input logic        fwd_valid,
    input logic [31:0] fwd_out,
    
    // Feedback path
    input logic [31:0] fb_in,
    input logic [31:0] fb_out,
    
    // Combined
    input logic [31:0] result
);

    // ============================================
    // TERMINATION PROPERTY
    // ============================================
    
    // Feedback loops must eventually converge
    property feedback_converges;
        @(posedge clk) disable iff (!rst_n)
        fwd_valid |-> ##[1:100] $stable(result);
    endproperty
    
    assert property (feedback_converges)
        else $error("Feedback loop doesn't converge");
    
    // ============================================
    // BOUNDED FEEDBACK
    // ============================================
    
    // Limit number of feedback iterations
    logic [7:0] iteration_count;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            iteration_count <= 0;
        else if (fwd_valid)
            iteration_count <= 0;
        else if (fb_out != fb_in)
            iteration_count <= iteration_count + 1;
    end
    
    property bounded_iterations;
        @(posedge clk) disable iff (!rst_n)
        iteration_count < 20;
    endproperty
    
    assert property (bounded_iterations)
        else $error("Too many feedback iterations");

endmodule

// ============================================
// REAL-WORLD EXAMPLE: CACHE + MEMORY
// ============================================

module cache_memory_composition (
    input logic        clk,
    input logic        rst_n,
    
    // CPU → Cache
    input logic [31:0] cpu_addr,
    input logic        cpu_req,
    input logic [31:0] cpu_rdata,
    input logic        cpu_valid,
    
    // Cache → Memory
    input logic [31:0] mem_addr,
    input logic        mem_req,
    input logic [31:0] mem_rdata,
    input logic        mem_valid,
    
    // Cache internal
    input logic        cache_hit,
    input logic        cache_miss
);

    // ============================================
    // CACHE CONTRACT
    // ============================================
    
    // Assumptions about CPU
    assume property (@(posedge clk) disable iff (!rst_n)
        cpu_req |-> !$isunknown(cpu_addr)
    );
    
    // Assumptions about Memory (from memory's guarantees)
    assume property (@(posedge clk) disable iff (!rst_n)
        mem_req |-> ##[1:20] mem_valid
    );
    
    // Cache Guarantees
    assert property (@(posedge clk) disable iff (!rst_n)
        cpu_req |-> ##[1:30] cpu_valid
    );
    
    // ============================================
    // MEMORY CONTRACT
    // ============================================
    
    // Assumptions
    assume property (@(posedge clk) disable iff (!rst_n)
        mem_req |-> !$isunknown(mem_addr)
    );
    
    // Guarantees
    assert property (@(posedge clk) disable iff (!rst_n)
        mem_req |-> ##[1:20] mem_valid
    );
    
    // ============================================
    // COMPOSED SYSTEM PROPERTY
    // ============================================
    
    // Cache hit: fast response
    property cache_hit_latency;
        @(posedge clk) disable iff (!rst_n)
        cpu_req && cache_hit |-> ##[1:3] cpu_valid;
    endproperty
    
    assert property (cache_hit_latency);
    
    // Cache miss: slower (includes memory access)
    property cache_miss_latency;
        @(posedge clk) disable iff (!rst_n)
        cpu_req && cache_miss |-> ##[1:30] cpu_valid;
    endproperty
    
    assert property (cache_miss_latency);

endmodule

// ============================================
// USAGE NOTES
// ============================================

/*
 * Compositional Verification Benefits:
 *
 * 1. SCALABILITY
 *    - Verify large systems by breaking into pieces
 *    - Each piece verified independently
 *    - State space explosion avoided
 *
 * 2. REUSABILITY
 *    - Module contracts reused in different systems
 *    - VIP (Verification IP) approach
 *    - Library of verified components
 *
 * 3. MODULARITY
 *    - Change one module without re-verifying all
 *    - Parallel verification possible
 *    - Team can work independently
 *
 * 4. CLARITY
 *    - Clear interface specifications
 *    - Documented assumptions and guarantees
 *    - Easier debugging
 *
 * Compositional Reasoning Rules:
 *
 * Sequential Composition (A → B):
 *   If A guarantees P
 *   And B assumes P
 *   Then A → B is correct
 *
 * Parallel Composition (A || B):
 *   If A and B don't interfere
 *   And both satisfy their contracts
 *   Then A || B is correct
 *
 * Hierarchical Composition:
 *   Bottom-up: Verify leaves, then compose
 *   Top-down: Decompose, verify pieces
 *
 * Challenges:
 *
 * 1. Finding right abstraction level
 * 2. Ensuring assumptions are met
 * 3. Handling circular dependencies
 * 4. Feedback loops need special care
 *
 * Best Practices:
 *
 * 1. Define clear interfaces
 * 2. Document all assumptions
 * 3. Verify contracts are compatible
 * 4. Use standard protocols where possible
 * 5. Start simple, add complexity gradually
 * 6. Verify composition points explicitly
 */
