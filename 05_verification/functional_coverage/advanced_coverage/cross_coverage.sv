// ============================================================================
// cross_coverage.sv - Cross Coverage Between Multiple Coverpoints
// ============================================================================

module cross_coverage;
    
    // ========================================================================
    // Basic Cross Coverage
    // ========================================================================
    
    class basic_cross;
        rand bit [1:0] a;
        rand bit [1:0] b;
        
        covergroup cg;
            cp_a: coverpoint a;
            cp_b: coverpoint b;
            
            // Cross coverage: all combinations of a and b
            cross_ab: cross cp_a, cp_b;
            // Creates bins for: (0,0), (0,1), (0,2), (0,3),
            //                   (1,0), (1,1), (1,2), (1,3), etc.
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Cross with Bins
    // ========================================================================
    
    class cross_with_bins;
        rand bit [2:0] mode;
        rand bit [7:0] data;
        
        covergroup cg;
            cp_mode: coverpoint mode {
                bins low_mode = {[0:3]};
                bins high_mode = {[4:7]};
            }
            
            cp_data: coverpoint data {
                bins small = {[0:63]};
                bins medium = {[64:191]};
                bins large = {[192:255]};
            }
            
            // Cross with explicit bin definitions
            cross_mode_data: cross cp_mode, cp_data;
            // Creates: (low_mode, small), (low_mode, medium), (low_mode, large),
            //          (high_mode, small), (high_mode, medium), (high_mode, large)
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Cross with Bins Selection
    // ========================================================================
    
    class cross_bins_selection;
        rand bit write;
        rand bit [1:0] size;
        
        covergroup cg;
            cp_write: coverpoint write {
                bins read = {0};
                bins write = {1};
            }
            
            cp_size: coverpoint size {
                bins byte_xfer = {0};
                bins half_xfer = {1};
                bins word_xfer = {2};
                bins dword_xfer = {3};
            }
            
            // Cross with custom bins
            cross_wr_size: cross cp_write, cp_size {
                // Only interested in specific combinations
                bins write_word = binsof(cp_write.write) && binsof(cp_size.word_xfer);
                bins write_dword = binsof(cp_write.write) && binsof(cp_size.dword_xfer);
                bins read_any = binsof(cp_write.read);
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Cross with Ignore Bins
    // ========================================================================
    
    class cross_ignore_bins;
        rand bit [1:0] op;
        rand bit [1:0] priority;
        
        covergroup cg;
            cp_op: coverpoint op {
                bins idle = {0};
                bins read = {1};
                bins write = {2};
                bins error = {3};
            }
            
            cp_priority: coverpoint priority {
                bins low = {0};
                bins medium = {1};
                bins high = {2};
                bins critical = {3};
            }
            
            cross_op_priority: cross cp_op, cp_priority {
                // Ignore nonsensical combinations
                ignore_bins idle_has_no_priority = binsof(cp_op.idle);
                ignore_bins error_priority = binsof(cp_op.error);
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Cross with Illegal Bins
    // ========================================================================
    
    class cross_illegal_bins;
        rand bit [1:0] mode;
        rand bit [1:0] burst_type;
        
        covergroup cg;
            cp_mode: coverpoint mode {
                bins fixed = {0};
                bins incr = {1};
                bins wrap = {2};
                bins reserved = {3};
            }
            
            cp_burst: coverpoint burst_type {
                bins single = {0};
                bins burst4 = {1};
                bins burst8 = {2};
                bins burst16 = {3};
            }
            
            cross_mode_burst: cross cp_mode, cp_burst {
                // Reserved mode with any burst is illegal
                illegal_bins bad_combo = binsof(cp_mode.reserved);
                
                // WRAP mode only valid with specific burst lengths
                illegal_bins wrap_single = binsof(cp_mode.wrap) && binsof(cp_burst.single);
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Three-Way Cross Coverage
    // ========================================================================
    
    class three_way_cross;
        rand bit write;
        rand bit [1:0] size;
        rand bit [1:0] burst;
        
        covergroup cg;
            cp_write: coverpoint write;
            cp_size: coverpoint size;
            cp_burst: coverpoint burst;
            
            // Three-way cross
            cross_all: cross cp_write, cp_size, cp_burst;
            // Creates 2 * 4 * 4 = 32 bins
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Cross with Conditional (iff)
    // ========================================================================
    
    class cross_conditional;
        rand bit [7:0] addr;
        rand bit [7:0] data;
        rand bit valid;
        
        covergroup cg;
            cp_addr: coverpoint addr {
                bins low = {[0:127]};
                bins high = {[128:255]};
            }
            
            cp_data: coverpoint data {
                bins zeros = {0};
                bins non_zeros = {[1:255]};
            }
            
            // Only cross when valid
            cross_addr_data: cross cp_addr, cp_data iff (valid);
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Cross Coverage Options
    // ========================================================================
    
    class cross_options;
        rand bit [2:0] a;
        rand bit [2:0] b;
        
        covergroup cg;
            cp_a: coverpoint a;
            cp_b: coverpoint b;
            
            cross_ab: cross cp_a, cp_b {
                option.weight = 10;      // Higher weight in coverage calculation
                option.goal = 95;        // 95% goal for this cross
                option.at_least = 2;     // At least 2 hits per cross bin
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Enum Cross Coverage
    // ========================================================================
    
    typedef enum bit [1:0] {IDLE, ACTIVE, WAIT, ERROR} state_e;
    typedef enum bit [1:0] {READ, WRITE, RMW, PREFETCH} cmd_e;
    
    class enum_cross;
        rand state_e state;
        rand cmd_e command;
        
        covergroup cg;
            cp_state: coverpoint state;
            cp_cmd: coverpoint command;
            
            // Cross enums
            cross_state_cmd: cross cp_state, cp_cmd {
                // Valid combinations
                bins active_read = binsof(cp_state.ACTIVE) && binsof(cp_cmd.READ);
                bins active_write = binsof(cp_state.ACTIVE) && binsof(cp_cmd.WRITE);
                bins active_rmw = binsof(cp_state.ACTIVE) && binsof(cp_cmd.RMW);
                
                // Illegal combinations
                illegal_bins idle_has_cmd = binsof(cp_state.IDLE) && 
                                           !binsof(cp_cmd) intersect {IDLE};
                illegal_bins error_ops = binsof(cp_state.ERROR);
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Cross with Expressions
    // ========================================================================
    
    class expression_cross;
        rand bit [7:0] a;
        rand bit [7:0] b;
        
        covergroup cg;
            cp_a_range: coverpoint a {
                bins low = {[0:127]};
                bins high = {[128:255]};
            }
            
            cp_b_range: coverpoint b {
                bins low = {[0:127]};
                bins high = {[128:255]};
            }
            
            // Cross based on comparison
            cp_compare: coverpoint (a > b) {
                bins a_greater = {1};
                bins b_greater_or_equal = {0};
            }
            
            // Cross ranges with comparison result
            cross_range_compare: cross cp_a_range, cp_b_range, cp_compare;
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Real-World Example: AXI Transaction Cross Coverage
    // ========================================================================
    
    typedef enum bit [1:0] {FIXED, INCR, WRAP} axi_burst_e;
    typedef enum bit [1:0] {OKAY, EXOKAY, SLVERR, DECERR} axi_resp_e;
    
    class axi_cross_coverage;
        rand bit write;
        rand bit [2:0] size;
        rand bit [7:0] len;
        rand axi_burst_e burst;
        rand axi_resp_e resp;
        rand bit [31:0] addr;
        
        covergroup cg;
            // Individual coverpoints
            cp_write: coverpoint write {
                bins read = {0};
                bins write = {1};
            }
            
            cp_size: coverpoint size {
                bins byte_sz = {0};
                bins half_sz = {1};
                bins word_sz = {2};
                bins dword_sz = {3};
            }
            
            cp_len: coverpoint len {
                bins single = {0};
                bins short_burst = {[1:7]};
                bins long_burst = {[8:255]};
            }
            
            cp_burst: coverpoint burst;
            cp_resp: coverpoint resp;
            
            cp_aligned: coverpoint addr[1:0] {
                bins aligned = {2'b00};
                bins unaligned = {2'b01, 2'b10, 2'b11};
            }
            
            // Cross: Write direction with size
            cross_wr_size: cross cp_write, cp_size {
                option.weight = 5;
            }
            
            // Cross: Burst type with length
            cross_burst_len: cross cp_burst, cp_len {
                // WRAP only valid with specific lengths
                illegal_bins wrap_invalid_len = binsof(cp_burst.WRAP) && 
                    !binsof(cp_len) intersect {1, 3, 7, 15};
            }
            
            // Cross: Size with alignment
            cross_size_align: cross cp_size, cp_aligned {
                // Larger sizes should be aligned
                illegal_bins word_unaligned = binsof(cp_size.word_sz) && 
                                             binsof(cp_aligned.unaligned);
                illegal_bins dword_unaligned = binsof(cp_size.dword_sz) && 
                                              binsof(cp_aligned.unaligned);
            }
            
            // Cross: Write with response (errors more common on writes)
            cross_wr_resp: cross cp_write, cp_resp;
            
            // Three-way cross: key transaction attributes
            cross_main_attrs: cross cp_write, cp_size, cp_burst {
                option.weight = 10;
                option.at_least = 2;
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
        
        function void sample();
            cg.sample();
        endfunction
        
        function void print_coverage();
            $display("\n=== AXI Cross Coverage ===");
            $display("Write x Size:     %0.2f%%", cg.cross_wr_size.get_coverage());
            $display("Burst x Length:   %0.2f%%", cg.cross_burst_len.get_coverage());
            $display("Size x Alignment: %0.2f%%", cg.cross_size_align.get_coverage());
            $display("Write x Response: %0.2f%%", cg.cross_wr_resp.get_coverage());
            $display("Main Attributes:  %0.2f%%", cg.cross_main_attrs.get_coverage());
            $display("Overall:          %0.2f%%", cg.get_coverage());
        endfunction
    endclass
    
    initial begin
        basic_cross basic;
        cross_with_bins bins_ex;
        cross_bins_selection sel;
        cross_ignore_bins ignore;
        three_way_cross three;
        enum_cross enums;
        axi_cross_coverage axi;
        
        $display("=== Cross Coverage Examples ===\n");
        
        // Basic cross
        $display("--- Basic Cross (2x2) ---");
        basic = new();
        repeat(100) begin
            assert(basic.randomize());
            basic.cg.sample();
        end
        $display("Cross coverage: %0.2f%%", basic.cg.cross_ab.get_coverage());
        
        // Cross with bins
        $display("\n--- Cross with Bins ---");
        bins_ex = new();
        repeat(200) begin
            assert(bins_ex.randomize());
            bins_ex.cg.sample();
        end
        $display("Cross coverage: %0.2f%%", bins_ex.cg.cross_mode_data.get_coverage());
        
        // Cross with selection
        $display("\n--- Cross with Bins Selection ---");
        sel = new();
        repeat(200) begin
            assert(sel.randomize());
            sel.cg.sample();
        end
        $display("Cross coverage: %0.2f%%", sel.cg.cross_wr_size.get_coverage());
        
        // Cross with ignore
        $display("\n--- Cross with Ignore Bins ---");
        ignore = new();
        repeat(200) begin
            assert(ignore.randomize());
            ignore.cg.sample();
        end
        $display("Cross coverage: %0.2f%%", ignore.cg.cross_op_priority.get_coverage());
        
        // Three-way cross
        $display("\n--- Three-Way Cross ---");
        three = new();
        repeat(300) begin
            assert(three.randomize());
            three.cg.sample();
        end
        $display("Cross coverage: %0.2f%%", three.cg.cross_all.get_coverage());
        
        // Enum cross
        $display("\n--- Enum Cross ---");
        enums = new();
        repeat(200) begin
            assert(enums.randomize());
            enums.cg.sample();
        end
        $display("Cross coverage: %0.2f%%", enums.cg.cross_state_cmd.get_coverage());
        
        // AXI example
        $display("\n--- AXI Cross Coverage ---");
        axi = new();
        repeat(2000) begin
            assert(axi.randomize());
            axi.sample();
        end
        axi.print_coverage();
    end
    
endmodule

/*
 * CROSS COVERAGE SYNTAX:
 * 
 * BASIC:
 *   cross cp1, cp2;
 * 
 * WITH NAME:
 *   cross_name: cross cp1, cp2;
 * 
 * WITH BINS SELECTION:
 *   cross_name: cross cp1, cp2 {
 *     bins name = binsof(cp1.bin1) && binsof(cp2.bin2);
 *   }
 * 
 * WITH IGNORE:
 *   cross_name: cross cp1, cp2 {
 *     ignore_bins name = binsof(cp1.bin1);
 *   }
 * 
 * WITH ILLEGAL:
 *   cross_name: cross cp1, cp2 {
 *     illegal_bins name = binsof(cp1.bin1) && binsof(cp2.bin2);
 *   }
 * 
 * KEY CONCEPTS:
 * 1. Cross creates bins for all combinations of coverpoint bins
 * 2. Number of cross bins = product of coverpoint bins
 * 3. Can cross 2+ coverpoints (2-way, 3-way, etc.)
 * 4. Use binsof() to select specific bins
 * 5. Use &&, ||, ! for bin selection logic
 * 
 * BINSOF() OPERATORS:
 * - &&: AND (both conditions must be true)
 * - ||: OR (either condition true)
 * - !:  NOT (negation)
 * - intersect: Set intersection
 * 
 * CROSS OPTIONS:
 * - option.weight: Relative importance
 * - option.goal: Target percentage
 * - option.at_least: Min hits per cross bin
 * 
 * BEST PRACTICES:
 * 1. Don't over-cross (exponential growth)
 * 2. Use ignore_bins for impossible combinations
 * 3. Use illegal_bins for invalid combinations
 * 4. Use binsof() to select meaningful combinations
 * 5. Consider three-way crosses carefully (can be huge)
 * 6. Weight important crosses higher
 * 
 * WHEN TO USE CROSS:
 * - Interactions between parameters matter
 * - Need to verify specific combinations
 * - Protocol rules depend on multiple fields
 * - Corner cases at combination boundaries
 * 
 * WHAT TO CROSS:
 * - Operation type x data size
 * - Address x transfer size x alignment
 * - Mode x configuration x state
 * - Error type x recovery action
 * - Priority x resource availability
 */
