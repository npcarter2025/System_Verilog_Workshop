// Safety Properties Examples
// "Bad things never happen"
// These properties assert that certain conditions should never occur

module safety_properties_examples #(
    parameter DEPTH = 16,
    parameter WIDTH = 32
) (
    input logic clk,
    input logic rst_n,
    
    // FIFO interface
    input logic push,
    input logic pop,
    input logic full,
    input logic empty,
    input logic [WIDTH-1:0] data_in,
    input logic [WIDTH-1:0] data_out,
    input logic [$clog2(DEPTH):0] count,
    
    // Arbiter interface
    input logic [3:0] req,
    input logic [3:0] grant,
    
    // State machine interface
    input logic [2:0] state
);

    // ============================================
    // FIFO SAFETY PROPERTIES
    // ============================================
    
    // Property: Never overflow (push when full)
    property no_overflow;
        @(posedge clk) disable iff (!rst_n)
        full |-> !push;
    endproperty
    
    assert_no_overflow: assert property (no_overflow)
        else $error("SAFETY VIOLATION: FIFO overflow - push occurred when full");
    
    // Property: Never underflow (pop when empty)
    property no_underflow;
        @(posedge clk) disable iff (!rst_n)
        empty |-> !pop;
    endproperty
    
    assert_no_underflow: assert property (no_underflow)
        else $error("SAFETY VIOLATION: FIFO underflow - pop occurred when empty");
    
    // Property: Full and empty are mutually exclusive
    property full_empty_mutex;
        @(posedge clk) disable iff (!rst_n)
        !(full && empty) || (DEPTH == 1);
    endproperty
    
    assert_full_empty_mutex: assert property (full_empty_mutex)
        else $error("SAFETY VIOLATION: FIFO is both full and empty");
    
    // Property: Count is within valid range
    property count_valid_range;
        @(posedge clk) disable iff (!rst_n)
        count <= DEPTH;
    endproperty
    
    assert_count_range: assert property (count_valid_range)
        else $error("SAFETY VIOLATION: Count exceeds FIFO depth");
    
    // ============================================
    // ARBITER SAFETY PROPERTIES
    // ============================================
    
    // Property: Mutual exclusion (at most one grant at a time)
    property mutex_grant;
        @(posedge clk) disable iff (!rst_n)
        $onehot0(grant);  // At most one bit is high
    endproperty
    
    assert_mutex: assert property (mutex_grant)
        else $error("SAFETY VIOLATION: Multiple grants active simultaneously");
    
    // Property: Only grant if requested
    property grant_implies_request;
        @(posedge clk) disable iff (!rst_n)
        (grant != 0) |-> ((grant & req) != 0);
    endproperty
    
    assert_grant_valid: assert property (grant_implies_request)
        else $error("SAFETY VIOLATION: Grant without corresponding request");
    
    // Property: Grant is subset of request
    property grant_subset_req;
        @(posedge clk) disable iff (!rst_n)
        (grant & ~req) == 0;
    endproperty
    
    assert_grant_subset: assert property (grant_subset_req)
        else $error("SAFETY VIOLATION: Grant bit set without request");
    
    // ============================================
    // STATE MACHINE SAFETY PROPERTIES
    // ============================================
    
    // Property: State is always valid (no illegal encodings)
    property valid_state_encoding;
        @(posedge clk) disable iff (!rst_n)
        state inside {3'b000, 3'b001, 3'b010, 3'b011, 3'b100};
    endproperty
    
    assert_valid_state: assert property (valid_state_encoding)
        else $error("SAFETY VIOLATION: Invalid state encoding detected");
    
    // Property: No undefined state values
    property no_x_in_state;
        @(posedge clk) disable iff (!rst_n)
        !$isunknown(state);
    endproperty
    
    assert_defined_state: assert property (no_x_in_state)
        else $error("SAFETY VIOLATION: State contains X or Z values");
    
    // ============================================
    // GENERAL SAFETY PROPERTIES
    // ============================================
    
    // Property: Data integrity - no X propagation
    property no_x_on_data;
        @(posedge clk) disable iff (!rst_n)
        push |-> !$isunknown(data_in);
    endproperty
    
    assert_data_defined: assert property (no_x_on_data)
        else $error("SAFETY VIOLATION: Undefined data being pushed to FIFO");
    
    // Property: Count consistency with flags
    property count_empty_consistent;
        @(posedge clk) disable iff (!rst_n)
        (count == 0) == empty;
    endproperty
    
    assert_count_empty: assert property (count_empty_consistent)
        else $error("SAFETY VIOLATION: Count and empty flag inconsistent");
    
    property count_full_consistent;
        @(posedge clk) disable iff (!rst_n)
        (count == DEPTH) == full;
    endproperty
    
    assert_count_full: assert property (count_full_consistent)
        else $error("SAFETY VIOLATION: Count and full flag inconsistent");

endmodule
