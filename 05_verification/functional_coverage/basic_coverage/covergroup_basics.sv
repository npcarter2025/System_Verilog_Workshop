// ============================================================================
// covergroup_basics.sv - Functional Coverage Basics with Covergroups
// ============================================================================

module covergroup_basics;
    
    // ========================================================================
    // Basic Covergroup Syntax
    // ========================================================================
    
    class basic_transaction;
        rand bit [7:0] addr;
        rand bit [31:0] data;
        rand bit write;
        
        // Inline covergroup (most common style)
        covergroup cg_basic;
            // Cover single variable
            cp_addr: coverpoint addr;
            cp_data: coverpoint data;
            cp_write: coverpoint write;
        endgroup
        
        function new();
            cg_basic = new();
        endfunction
        
        function void sample();
            cg_basic.sample();
        endfunction
    endclass
    
    // ========================================================================
    // Covergroup with Options
    // ========================================================================
    
    class transaction_with_options;
        rand bit [3:0] opcode;
        rand bit [7:0] length;
        
        covergroup cg_options;
            // Set goal to 95% instead of default 100%
            option.goal = 95;
            
            // At least 2 hits per bin
            option.at_least = 2;
            
            // User-defined name
            option.name = "transaction_coverage";
            
            // Auto-sampling per instance (useful for sampling in class methods)
            option.per_instance = 1;
            
            cp_opcode: coverpoint opcode;
            cp_length: coverpoint length;
        endgroup
        
        function new();
            cg_options = new();
        endfunction
        
        function void sample();
            cg_options.sample();
        endfunction
    endclass
    
    // ========================================================================
    // Automatic vs Manual Sampling
    // ========================================================================
    
    class auto_sample_transaction;
        rand bit [3:0] value;
        
        // Automatic sampling on every class member change
        covergroup cg @ (value);  // Sample when value changes
            cp_value: coverpoint value;
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    class manual_sample_transaction;
        rand bit [3:0] value;
        
        covergroup cg;
            cp_value: coverpoint value;
        endgroup
        
        function new();
            cg = new();
        endfunction
        
        // Explicit sampling control
        function void do_sample();
            cg.sample();
        endfunction
    endclass
    
    // ========================================================================
    // Module-Level Covergroup
    // ========================================================================
    
    bit [2:0] module_signal;
    
    covergroup cg_module;
        cp_signal: coverpoint module_signal;
    endgroup
    
    // ========================================================================
    // Coverage Queries
    // ========================================================================
    
    class coverage_queries;
        rand bit [2:0] mode;
        
        covergroup cg;
            cp_mode: coverpoint mode {
                bins low = {[0:3]};
                bins high = {[4:7]};
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
        
        function void sample();
            cg.sample();
        endfunction
        
        function void print_coverage();
            real cov;
            
            // Get overall coverage
            cov = cg.get_coverage();
            $display("Overall coverage: %0.2f%%", cov);
            
            // Get coverpoint-specific coverage
            cov = cg.cp_mode.get_coverage();
            $display("Mode coverpoint coverage: %0.2f%%", cov);
            
            // Get instance coverage
            cov = cg.get_inst_coverage();
            $display("Instance coverage: %0.2f%%", cov);
        endfunction
    endclass
    
    // ========================================================================
    // Multiple Covergroups
    // ========================================================================
    
    class multi_covergroup_transaction;
        rand bit [7:0] addr;
        rand bit [31:0] data;
        rand bit write;
        
        // Separate coverage for different aspects
        covergroup cg_address;
            cp_addr: coverpoint addr;
        endgroup
        
        covergroup cg_data;
            cp_data: coverpoint data;
        endgroup
        
        covergroup cg_operation;
            cp_write: coverpoint write;
        endgroup
        
        function new();
            cg_address = new();
            cg_data = new();
            cg_operation = new();
        endfunction
        
        function void sample();
            cg_address.sample();
            cg_data.sample();
            cg_operation.sample();
        endfunction
        
        function real get_total_coverage();
            real total = 0;
            total += cg_address.get_coverage();
            total += cg_data.get_coverage();
            total += cg_operation.get_coverage();
            return total / 3.0;
        endfunction
    endclass
    
    // ========================================================================
    // Covergroup Start/Stop Control
    // ========================================================================
    
    class controllable_coverage;
        rand bit [3:0] value;
        
        covergroup cg;
            cp_value: coverpoint value;
        endgroup
        
        function new();
            cg = new();
        endfunction
        
        function void enable_coverage();
            cg.start();
            $display("Coverage enabled");
        endfunction
        
        function void disable_coverage();
            cg.stop();
            $display("Coverage disabled");
        endfunction
        
        function void sample();
            cg.sample();
        endfunction
    endclass
    
    // ========================================================================
    // Pass/Fail Arguments
    // ========================================================================
    
    class pass_fail_transaction;
        rand bit [2:0] status;
        bit success;
        
        covergroup cg (int threshold);
            cp_status: coverpoint status {
                bins pass_bins[] = {[0:threshold-1]};
                bins fail_bins[] = {[threshold:7]};
            }
        endgroup
        
        function new(int threshold = 4);
            cg = new(threshold);
        endfunction
        
        function void sample();
            cg.sample();
        endfunction
    endclass
    
    // ========================================================================
    // Real-World Example: Protocol Transaction
    // ========================================================================
    
    typedef enum bit [1:0] {READ, WRITE, IDLE, ERROR} op_e;
    
    class protocol_transaction;
        rand op_e operation;
        rand bit [7:0] addr;
        rand bit [31:0] data;
        rand bit [1:0] priority;
        
        covergroup cg_protocol;
            option.name = "protocol_coverage";
            option.comment = "Coverage for protocol transactions";
            
            // Operation coverage
            cp_op: coverpoint operation {
                bins read_op = {READ};
                bins write_op = {WRITE};
                bins idle_op = {IDLE};
                bins error_op = {ERROR};
            }
            
            // Address coverage
            cp_addr: coverpoint addr;
            
            // Priority coverage
            cp_priority: coverpoint priority {
                bins low = {0};
                bins medium = {1};
                bins high = {2};
                bins critical = {3};
            }
        endgroup
        
        function new();
            cg_protocol = new();
        endfunction
        
        function void sample();
            cg_protocol.sample();
        endfunction
        
        function void print_summary();
            $display("\n=== Coverage Summary ===");
            $display("Operation coverage: %0.2f%%", 
                    cg_protocol.cp_op.get_coverage());
            $display("Address coverage: %0.2f%%", 
                    cg_protocol.cp_addr.get_coverage());
            $display("Priority coverage: %0.2f%%", 
                    cg_protocol.cp_priority.get_coverage());
            $display("Overall coverage: %0.2f%%", 
                    cg_protocol.get_coverage());
        endfunction
    endclass
    
    initial begin
        basic_transaction basic;
        transaction_with_options opts;
        coverage_queries query;
        multi_covergroup_transaction multi;
        controllable_coverage ctrl;
        pass_fail_transaction pass_fail;
        protocol_transaction protocol;
        cg_module cg_mod;
        
        $display("=== Covergroup Basics Examples ===\n");
        
        // Basic covergroup
        $display("--- Basic Covergroup ---");
        basic = new();
        repeat(20) begin
            assert(basic.randomize());
            basic.sample();
        end
        $display("Coverage: %0.2f%%", basic.cg_basic.get_coverage());
        
        // With options
        $display("\n--- Covergroup with Options ---");
        opts = new();
        repeat(20) begin
            assert(opts.randomize());
            opts.sample();
        end
        $display("Coverage: %0.2f%%", opts.cg_options.get_coverage());
        
        // Coverage queries
        $display("\n--- Coverage Queries ---");
        query = new();
        repeat(30) begin
            assert(query.randomize());
            query.sample();
        end
        query.print_coverage();
        
        // Multiple covergroups
        $display("\n--- Multiple Covergroups ---");
        multi = new();
        repeat(20) begin
            assert(multi.randomize());
            multi.sample();
        end
        $display("Total coverage: %0.2f%%", multi.get_total_coverage());
        
        // Controllable coverage
        $display("\n--- Start/Stop Control ---");
        ctrl = new();
        ctrl.enable_coverage();
        repeat(10) begin
            assert(ctrl.randomize());
            ctrl.sample();
        end
        $display("Coverage with sampling: %0.2f%%", ctrl.cg.get_coverage());
        
        ctrl.disable_coverage();
        repeat(10) begin
            assert(ctrl.randomize());
            ctrl.sample();  // Won't count
        end
        $display("Coverage after stop: %0.2f%%", ctrl.cg.get_coverage());
        
        // Pass/fail with arguments
        $display("\n--- Pass/Fail (threshold=4) ---");
        pass_fail = new(4);
        repeat(30) begin
            assert(pass_fail.randomize());
            pass_fail.sample();
        end
        $display("Coverage: %0.2f%%", pass_fail.cg.get_coverage());
        
        // Module-level covergroup
        $display("\n--- Module-Level Covergroup ---");
        cg_mod = new();
        for (int i = 0; i < 8; i++) begin
            module_signal = i;
            cg_mod.sample();
        end
        $display("Module coverage: %0.2f%%", cg_mod.get_coverage());
        
        // Protocol example
        $display("\n--- Protocol Transaction Coverage ---");
        protocol = new();
        repeat(100) begin
            assert(protocol.randomize());
            protocol.sample();
        end
        protocol.print_summary();
    end
    
endmodule

/*
 * COVERGROUP FUNDAMENTALS:
 * 
 * BASIC SYNTAX:
 *   covergroup cg_name;
 *     coverpoint variable;
 *   endgroup
 * 
 * INSTANTIATION:
 *   cg_name = new();
 * 
 * SAMPLING:
 *   cg_name.sample();
 * 
 * KEY CONCEPTS:
 * 1. Covergroup: Container for coverage specification
 * 2. Coverpoint: What to measure (variable/expression)
 * 3. Bins: Categories within a coverpoint
 * 4. Sample: Event that records coverage
 * 
 * COVERGROUP OPTIONS:
 * - option.goal: Target coverage percentage (default 100)
 * - option.at_least: Minimum hits per bin (default 1)
 * - option.name: User-defined name
 * - option.comment: Description
 * - option.per_instance: Separate coverage per instance
 * 
 * SAMPLING METHODS:
 * 1. Manual: cg.sample() - explicit control
 * 2. Automatic: covergroup cg @ (event) - triggers on event
 * 3. Clocked: covergroup cg @ (posedge clk) - clock-based
 * 
 * COVERAGE QUERIES:
 * - get_coverage(): Overall coverage percentage
 * - get_inst_coverage(): Per-instance coverage
 * - coverpoint.get_coverage(): Specific coverpoint
 * 
 * CONTROL METHODS:
 * - start(): Enable coverage collection
 * - stop(): Disable coverage collection
 * - sample(): Record current values
 * 
 * LOCATION:
 * - Class member (most common)
 * - Module level
 * - Package level
 * 
 * BEST PRACTICES:
 * 1. Sample at meaningful transaction boundaries
 * 2. Use descriptive names for covergroups and coverpoints
 * 3. Set realistic goals (option.goal)
 * 4. Group related coverage together
 * 5. Use per_instance for multiple instances of same class
 * 
 * COMMON PATTERNS:
 * - One covergroup per class (transaction-level)
 * - Multiple covergroups for different aspects
 * - Module-level for interface signals
 * - Arguments for parameterized coverage
 */
