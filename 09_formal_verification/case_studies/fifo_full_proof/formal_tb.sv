// Formal Testbench for FIFO Verification
// Binds the FIFO DUT with formal properties

module fifo_formal_tb;

    parameter DEPTH = 16;
    parameter WIDTH = 32;
    
    // Clock and reset
    logic clk;
    logic rst_n;
    
    // FIFO interface signals
    logic             push;
    logic [WIDTH-1:0] wr_data;
    logic             full;
    logic             almost_full;
    
    logic             pop;
    logic [WIDTH-1:0] rd_data;
    logic             empty;
    logic             almost_empty;
    
    logic [$clog2(DEPTH):0] count;
    
    // ============================================
    // DUT INSTANTIATION
    // ============================================
    
    sync_fifo #(
        .DEPTH(DEPTH),
        .WIDTH(WIDTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .push(push),
        .wr_data(wr_data),
        .full(full),
        .almost_full(almost_full),
        .pop(pop),
        .rd_data(rd_data),
        .empty(empty),
        .almost_empty(almost_empty),
        .count(count)
    );
    
    // ============================================
    // CLOCK GENERATION (for bounded model checking)
    // ============================================
    
    // In formal verification, clock is symbolic
    // But we define it for simulation compatibility
    
    initial clk = 0;
    always #5 clk = ~clk;
    
    // ============================================
    // RESET GENERATION
    // ============================================
    
    initial begin
        rst_n = 0;
        #20;
        rst_n = 1;
    end
    
    // ============================================
    // FORMAL PROPERTIES BINDING
    // ============================================
    
    fifo_formal_properties #(
        .DEPTH(DEPTH),
        .WIDTH(WIDTH)
    ) formal_checker (
        .clk(clk),
        .rst_n(rst_n),
        .push(push),
        .wr_data(wr_data),
        .full(full),
        .almost_full(almost_full),
        .pop(pop),
        .rd_data(rd_data),
        .empty(empty),
        .almost_empty(almost_empty),
        .count(count)
    );
    
    // ============================================
    // FORMAL CONSTRAINTS (ASSUMPTIONS)
    // ============================================
    
    // These constrain the input stimulus for formal verification
    
    // Assumption: Don't push when full (well-behaved environment)
    property assume_no_illegal_push;
        @(posedge clk) disable iff (!rst_n)
        full |-> !push;
    endproperty
    
    assume_push: assume property (assume_no_illegal_push);
    
    // Assumption: Don't pop when empty (well-behaved environment)  
    property assume_no_illegal_pop;
        @(posedge clk) disable iff (!rst_n)
        empty |-> !pop;
    endproperty
    
    assume_pop: assume property (assume_no_illegal_pop);
    
    // Assumption: Write data is defined (no X/Z)
    property assume_data_defined;
        @(posedge clk) disable iff (!rst_n)
        push |-> !$isunknown(wr_data);
    endproperty
    
    assume_wr_data: assume property (assume_data_defined);
    
    // ============================================
    // SIMULATION STIMULUS (for waveform debugging)
    // ============================================
    
    // This section is for simulation only - ignored by formal tools
    
    `ifndef FORMAL_VERIFICATION
    
    initial begin
        // Initialize
        push = 0;
        pop = 0;
        wr_data = 0;
        
        @(posedge rst_n);
        repeat(2) @(posedge clk);
        
        // Test 1: Fill the FIFO
        $display("Test 1: Filling FIFO");
        repeat(DEPTH) begin
            @(posedge clk);
            push = 1;
            wr_data = $urandom();
        end
        @(posedge clk);
        push = 0;
        
        // Check full
        assert(full) else $error("FIFO should be full");
        
        // Test 2: Drain the FIFO
        $display("Test 2: Draining FIFO");
        repeat(DEPTH) begin
            @(posedge clk);
            pop = 1;
        end
        @(posedge clk);
        pop = 0;
        
        // Check empty
        assert(empty) else $error("FIFO should be empty");
        
        // Test 3: Simultaneous push/pop
        $display("Test 3: Simultaneous operations");
        repeat(10) begin
            @(posedge clk);
            push = $random() % 2;
            pop = $random() % 2;
            if (push) wr_data = $urandom();
        end
        
        // Test 4: Random operations
        $display("Test 4: Random operations");
        repeat(100) begin
            @(posedge clk);
            push = !full && ($random() % 2);
            pop = !empty && ($random() % 2);
            if (push) wr_data = $urandom();
        end
        
        $display("Simulation complete");
        $finish;
    end
    
    // Waveform dumping
    initial begin
        $dumpfile("fifo_formal.vcd");
        $dumpvars(0, fifo_formal_tb);
    end
    
    // Timeout
    initial begin
        #100000;
        $display("Timeout!");
        $finish;
    end
    
    `endif
    
    // ============================================
    // FORMAL VERIFICATION DIRECTIVES
    // ============================================
    
    // These are tool-specific hints for formal verification
    
    // For JasperGold:
    // set_engine_mode {Hp Ht B I N}
    // set_prove_time_limit 3600
    // prove -all
    
    // For VC Formal:
    // set_formal_mode setup
    // set_formal_property_depth 50
    // prove -all
    
    // Expected depth for complete proof: 2*DEPTH+10 cycles
    // This allows filling and draining the FIFO with margin

endmodule

// ============================================
// FORMAL VERIFICATION SCRIPT EXAMPLE
// ============================================

/*
# Example JasperGold TCL Script
# Save as: fifo_formal.tcl

# Clear previous
clear -all

# Analyze design
analyze -sv09 \
    fifo_model.sv \
    fifo_properties.sv \
    formal_tb.sv

# Elaborate
elaborate -top fifo_formal_tb

# Set up clocks
clock clk
reset -expression {!rst_n}

# Set depth for bounded model checking
set_prove_time_limit 3600
set_max_trace_length 50

# Prove all assertions
prove -all

# Check all covers
task -show cover
prove -cover -all

# Generate report
report -file fifo_formal_report.txt

# Generate counterexample if any failures
if {[get_property status [current_task]] == "proven_false"} {
    visualize -counterexample -task <task_name> -window
}
*/

// ============================================
// EXPECTED RESULTS
// ============================================

/*
 * All assertions should PROVE:
 *   ✓ no_overflow
 *   ✓ no_underflow
 *   ✓ full_empty_mutex
 *   ✓ count_empty_consistent
 *   ✓ count_full_consistent
 *   ✓ almost_empty_correct
 *   ✓ almost_full_correct
 *   ✓ count_valid
 *   ✓ push_increments
 *   ✓ pop_decrements
 *   ✓ simultaneous_stable
 *   ✓ no_op_stable
 *   ✓ data_integrity
 *   ✓ shadow_count_match
 *   ✓ reset_to_empty
 *   ✓ reset_not_full
 *
 * All covers should be REACHABLE:
 *   ✓ full
 *   ✓ full_to_empty
 *   ✓ consec_push
 *   ✓ consec_pop
 *   ✓ simul
 *   ✓ push_almost_full
 *   ✓ pop_almost_empty
 *   ✓ fill
 *   ✓ drain
 *
 * If any assertion fails, the tool will provide a counterexample
 * showing the exact sequence of inputs that triggers the bug.
 *
 * If any cover is unreachable, it indicates either:
 *   1. Over-constrained assumptions
 *   2. Insufficient depth
 *   3. Actual design limitation
 */

// ============================================
// DEBUGGING TIPS
// ============================================

/*
 * 1. Start with small DEPTH (e.g., 4) for faster convergence
 * 2. If proof doesn't converge, try:
 *    - Increase depth limit
 *    - Add more assumptions
 *    - Simplify properties (prove subset first)
 * 3. Use cover properties to ensure assertions are exercised
 * 4. Check for vacuous passes (assertion never triggers)
 * 5. View waveforms of counterexamples to understand failures
 */
