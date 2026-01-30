// ============================================================================
// ignore_bins.sv - Ignore Bins for Excluding Values from Coverage
// ============================================================================

module ignore_bins;
    
    // ========================================================================
    // Basic Ignore Bins
    // ========================================================================
    
    class basic_ignore;
        rand bit [3:0] value;
        
        covergroup cg;
            cp_value: coverpoint value {
                bins low = {[0:7]};
                bins high = {[8:15]};
                
                // Don't track these values in coverage
                ignore_bins dont_care = {13, 14};
                // These values can occur, but won't affect coverage %
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Ignore Reserved/Debug Values
    // ========================================================================
    
    class ignore_reserved;
        rand bit [7:0] opcode;
        
        covergroup cg;
            cp_opcode: coverpoint opcode {
                bins arithmetic = {[0:31]};
                bins logical = {[32:63]};
                bins memory = {[64:95]};
                bins branch = {[96:127]};
                
                // Reserved for future use - ignore these
                ignore_bins reserved = {[128:255]};
                // Won't error if seen, just won't count toward coverage
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Ignore Specific Transitions
    // ========================================================================
    
    typedef enum bit [1:0] {IDLE, ACTIVE, WAIT, DONE} state_e;
    
    class ignore_transitions;
        state_e state;
        
        covergroup cg;
            cp_state: coverpoint state {
                bins idle = {IDLE};
                bins active = {ACTIVE};
                bins wait_st = {WAIT};
                bins done = {DONE};
                
                // Interesting transitions
                bins start = (IDLE => ACTIVE);
                bins finish = (ACTIVE => DONE);
                bins restart = (DONE => IDLE);
                
                // Ignore self-loops (not interesting)
                ignore_bins self_idle = (IDLE => IDLE);
                ignore_bins self_active = (ACTIVE => ACTIVE);
                ignore_bins self_wait = (WAIT => WAIT);
                ignore_bins self_done = (DONE => DONE);
            }
        endgroup
        
        function new();
            cg = new();
            state = IDLE;
        endfunction
        
        function void next(state_e s);
            state = s;
            cg.sample();
        endfunction
    endclass
    
    // ========================================================================
    // Ignore in Cross Coverage
    // ========================================================================
    
    class ignore_cross;
        rand bit [1:0] op_type;
        rand bit [1:0] priority;
        
        covergroup cg;
            cp_op: coverpoint op_type {
                bins idle = {0};
                bins read = {1};
                bins write = {2};
                bins special = {3};
            }
            
            cp_priority: coverpoint priority {
                bins low = {0};
                bins medium = {1};
                bins high = {2};
                bins critical = {3};
            }
            
            cross_op_pri: cross cp_op, cp_priority {
                // IDLE operations don't have meaningful priority
                ignore_bins idle_pri = binsof(cp_op.idle);
                
                // SPECIAL operations always critical, so other priorities don't matter
                ignore_bins special_non_crit = binsof(cp_op.special) && 
                    !binsof(cp_priority.critical);
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Ignore Based on Conditions
    // ========================================================================
    
    class ignore_conditional;
        rand bit [7:0] data;
        bit debug_mode;
        bit test_mode;
        
        covergroup cg;
            // In normal mode, track all values
            cp_normal: coverpoint data iff (!debug_mode && !test_mode) {
                bins low = {[0:63]};
                bins mid = {[64:191]};
                bins high = {[192:255]};
            }
            
            // In debug mode, ignore certain ranges
            cp_debug: coverpoint data iff (debug_mode) {
                bins debug_low = {[0:15]};
                bins debug_high = {[240:255]};
                
                // Ignore middle range in debug mode (not interesting)
                ignore_bins debug_middle = {[16:239]};
            }
            
            // In test mode, only track corner cases
            cp_test: coverpoint data iff (test_mode) {
                bins corners = {0, 1, 254, 255};
                
                // Ignore everything else
                ignore_bins test_middle = {[2:253]};
            }
        endgroup
        
        function new();
            cg = new();
            debug_mode = 0;
            test_mode = 0;
        endfunction
    endclass
    
    // ========================================================================
    // Ignore Don't-Care Values
    // ========================================================================
    
    class ignore_dont_care;
        rand bit [3:0] config;
        rand bit [3:0] status;
        
        covergroup cg;
            cp_config: coverpoint config {
                bins cfg0 = {0};
                bins cfg1 = {1};
                bins cfg2 = {2};
                bins cfg_high[] = {[3:12]};
                
                // Values 13-15 are don't-care for config
                ignore_bins cfg_unused = {[13:15]};
            }
            
            cp_status: coverpoint status {
                bins idle = {0};
                bins busy = {1};
                bins done = {2};
                bins error = {3};
                
                // Status values 4-15 undefined, but might occur during resets
                ignore_bins status_undefined = {[4:15]};
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Ignore Redundant Combinations
    // ========================================================================
    
    typedef enum bit [1:0] {READ, WRITE, RMW, PREFETCH} cmd_e;
    
    class ignore_redundant;
        rand cmd_e command;
        rand bit [1:0] size;
        rand bit cacheable;
        
        covergroup cg;
            cp_cmd: coverpoint command;
            
            cp_size: coverpoint size {
                bins byte_sz = {0};
                bins half_sz = {1};
                bins word_sz = {2};
                bins dword_sz = {3};
            }
            
            cp_cacheable: coverpoint cacheable;
            
            // PREFETCH doesn't use size field
            cross_cmd_size: cross cp_cmd, cp_size {
                ignore_bins prefetch_size = binsof(cp_cmd.PREFETCH);
            }
            
            // READ operations: cacheable flag is the interesting part
            // For WRITE operations: cacheable doesn't matter much
            cross_cmd_cache: cross cp_cmd, cp_cacheable {
                // These combinations exist but aren't interesting
                ignore_bins write_cache_dont_care = binsof(cp_cmd.WRITE);
                ignore_bins rmw_cache_dont_care = binsof(cp_cmd.RMW);
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Ignore Wildcards
    // ========================================================================
    
    class ignore_wildcard;
        rand bit [7:0] pattern;
        
        covergroup cg;
            cp_pattern: coverpoint pattern {
                wildcard bins pattern_a = {8'b0000_????};
                wildcard bins pattern_b = {8'b0001_????};
                wildcard bins pattern_c = {8'b001?_????};
                
                // Ignore debug patterns
                wildcard ignore_bins debug_patterns = {8'b1111_????};
                
                // Ignore specific test patterns
                wildcard ignore_bins test_patterns = {8'b1110_0000, 8'b1110_1111};
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Ignore for Performance (Reduce Coverage Space)
    // ========================================================================
    
    class ignore_for_performance;
        rand bit [15:0] addr;
        
        covergroup cg;
            cp_addr: coverpoint addr {
                // Only interested in page boundaries
                bins page_boundaries[] = {16'h0000, 16'h1000, 16'h2000, 16'h3000,
                                         16'h4000, 16'h5000, 16'h6000, 16'h7000,
                                         16'h8000, 16'h9000, 16'hA000, 16'hB000,
                                         16'hC000, 16'hD000, 16'hE000, 16'hF000};
                
                // Ignore all other addresses (too many to track individually)
                ignore_bins non_boundaries = default;
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Real-World: AXI with Ignore Bins
    // ========================================================================
    
    typedef enum bit [1:0] {FIXED, INCR, WRAP} burst_e;
    typedef enum bit [1:0] {OKAY, EXOKAY, SLVERR, DECERR} resp_e;
    
    class axi_with_ignore;
        rand bit write;
        rand bit [2:0] size;
        rand bit [7:0] len;
        rand burst_e burst;
        rand resp_e resp;
        rand bit [31:0] addr;
        rand bit [3:0] cache;
        rand bit [2:0] prot;
        
        covergroup cg;
            cp_write: coverpoint write;
            
            cp_size: coverpoint size {
                bins byte_sz = {0};
                bins half_sz = {1};
                bins word_sz = {2};
                bins dword_sz = {3};
            }
            
            cp_len: coverpoint len {
                bins single = {0};
                bins short_burst = {[1:7]};
                bins medium_burst = {[8:15]};
                bins long_burst = {[16:255]};
            }
            
            cp_burst: coverpoint burst;
            cp_resp: coverpoint resp;
            
            cp_cache: coverpoint cache {
                bins non_cacheable = {4'b0000};
                bins write_through = {4'b0110};
                bins write_back = {4'b1110};
                
                // Ignore other cache encodings (less common)
                ignore_bins cache_other = default;
            }
            
            cp_prot: coverpoint prot {
                bins normal = {3'b000};
                bins privileged = {3'b001};
                
                // Ignore secure/non-secure variations (not focus of test)
                ignore_bins prot_variations = default;
            }
            
            // Address ranges
            cp_addr_region: coverpoint addr {
                bins low_mem = {[32'h0000_0000:32'h0FFF_FFFF]};
                bins mid_mem = {[32'h1000_0000:32'h7FFF_FFFF]};
                bins high_mem = {[32'h8000_0000:32'hFFFF_FFFF]};
            }
            
            // Cross: burst type with length
            cross_burst_len: cross cp_burst, cp_len {
                // FIXED bursts: length doesn't matter much
                ignore_bins fixed_len_dont_care = binsof(cp_burst.FIXED);
            }
            
            // Cross: response with transaction type
            cross_write_resp: cross cp_write, cp_resp {
                // Exclusive responses only for special transactions
                ignore_bins exokay = binsof(cp_resp.EXOKAY);
            }
            
            // Cross: size with address
            cross_size_addr: cross cp_size, cp_addr_region {
                // Not tracking size per region (too many bins)
                ignore_bins size_per_region = binsof(cp_addr_region.mid_mem) || 
                                              binsof(cp_addr_region.high_mem);
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
        
        function void sample();
            cg.sample();
        endfunction
        
        function void print_coverage();
            $display("\n=== AXI Coverage (with Ignore Bins) ===");
            $display("Write:        %0.2f%%", cg.cp_write.get_coverage());
            $display("Size:         %0.2f%%", cg.cp_size.get_coverage());
            $display("Length:       %0.2f%%", cg.cp_len.get_coverage());
            $display("Burst:        %0.2f%%", cg.cp_burst.get_coverage());
            $display("Response:     %0.2f%%", cg.cp_resp.get_coverage());
            $display("Cache:        %0.2f%%", cg.cp_cache.get_coverage());
            $display("Protection:   %0.2f%%", cg.cp_prot.get_coverage());
            $display("Overall:      %0.2f%%", cg.get_coverage());
        endfunction
    endclass
    
    initial begin
        basic_ignore basic;
        ignore_reserved reserved;
        ignore_transitions trans;
        ignore_cross xcross;
        ignore_conditional cond;
        ignore_redundant redund;
        axi_with_ignore axi;
        
        $display("=== Ignore Bins Examples ===\n");
        
        // Basic
        $display("--- Basic Ignore Bins ---");
        basic = new();
        repeat(100) begin
            assert(basic.randomize());
            basic.cg.sample();
        end
        $display("Coverage: %0.2f%% (values 13,14 ignored)", 
                basic.cg.get_coverage());
        
        // Reserved
        $display("\n--- Ignore Reserved Values ---");
        reserved = new();
        repeat(200) begin
            assert(reserved.randomize());
            reserved.cg.sample();
        end
        $display("Coverage: %0.2f%% (128-255 ignored)", 
                reserved.cg.get_coverage());
        
        // Transitions
        $display("\n--- Ignore Self-Transitions ---");
        trans = new();
        trans.next(IDLE);
        trans.next(IDLE);  // Ignored
        trans.next(ACTIVE);
        trans.next(ACTIVE);  // Ignored
        trans.next(DONE);
        trans.next(DONE);  // Ignored
        trans.next(IDLE);
        $display("Coverage: %0.2f%% (self-loops ignored)", 
                trans.cg.get_coverage());
        
        // Cross
        $display("\n--- Ignore in Cross Coverage ---");
        xcross = new();
        repeat(200) begin
            assert(xcross.randomize());
            xcross.cg.sample();
        end
        $display("Coverage: %0.2f%% (idle priority ignored)", 
                xcross.cg.get_coverage());
        
        // Conditional
        $display("\n--- Mode-Dependent Ignore ---");
        cond = new();
        cond.debug_mode = 0;
        repeat(50) begin
            assert(cond.randomize());
            cond.cg.sample();
        end
        cond.debug_mode = 1;
        repeat(50) begin
            assert(cond.randomize());
            cond.cg.sample();
        end
        $display("Coverage: %0.2f%%", cond.cg.get_coverage());
        
        // Redundant
        $display("\n--- Ignore Redundant Combinations ---");
        redund = new();
        repeat(200) begin
            assert(redund.randomize());
            redund.cg.sample();
        end
        $display("Coverage: %0.2f%% (prefetch size, write cache ignored)", 
                redund.cg.get_coverage());
        
        // AXI
        $display("\n--- AXI with Ignore Bins ---");
        axi = new();
        repeat(1000) begin
            assert(axi.randomize());
            axi.sample();
        end
        axi.print_coverage();
    end
    
endmodule

/*
 * IGNORE_BINS SYNTAX:
 * 
 * BASIC:
 *   ignore_bins name = {values};
 * 
 * RANGE:
 *   ignore_bins name = {[start:end]};
 * 
 * DEFAULT:
 *   ignore_bins name = default;
 * 
 * WILDCARD:
 *   wildcard ignore_bins name = {pattern};
 * 
 * TRANSITIONS:
 *   ignore_bins name = (val1 => val2);
 * 
 * IN CROSS:
 *   ignore_bins name = binsof(cp1) && binsof(cp2);
 * 
 * PURPOSE:
 * 1. Exclude don't-care values from coverage
 * 2. Focus coverage on interesting cases
 * 3. Reduce coverage space (performance)
 * 4. Ignore reserved/undefined values
 * 5. Skip redundant combinations
 * 
 * BEHAVIOR:
 * - Ignored values CAN occur (not an error)
 * - They just don't count toward coverage %
 * - Effectively removed from coverage calculation
 * - No warning/error when sampled
 * 
 * IGNORE_BINS vs ILLEGAL_BINS:
 * - ignore_bins: Value can occur, don't care (neutral)
 * - illegal_bins: Value should NOT occur (error detection)
 * 
 * WHEN TO USE:
 * - Don't-care values (reserved for future)
 * - Debug/test-only values
 * - Redundant combinations
 * - Self-loops in state machines
 * - Performance: reduce coverage space
 * - Values that occur but aren't interesting
 * 
 * BEST PRACTICES:
 * 1. Document WHY value is ignored
 * 2. Use to focus on important scenarios
 * 3. Reduce bins for large address spaces
 * 4. Ignore self-transitions if not interesting
 * 5. Ignore redundant cross combinations
 * 6. Review periodically (might become interesting later)
 * 
 * COMMON PATTERNS:
 * - Reserved: ignore_bins reserved = {[high:max]};
 * - Debug: ignore_bins debug = {debug_vals} iff (!production);
 * - Self-loops: ignore_bins self = (STATE => STATE);
 * - Don't care cross: ignore_bins = binsof(a) && binsof(b);
 * - Default: ignore_bins rest = default;
 * 
 * COVERAGE IMPACT:
 * - Reduces total number of bins
 * - Makes 100% coverage more achievable
 * - Focuses effort on important cases
 * - Can significantly reduce runtime
 * 
 * TRADE-OFFS:
 * + Pros:
 *   - Faster coverage closure
 *   - Focus on important cases
 *   - Reduced memory/performance overhead
 * - Cons:
 *   - Might miss unexpected scenarios
 *   - Need to review what's ignored
 *   - Can hide interesting bugs
 * 
 * WHEN NOT TO USE:
 * - Don't ignore without good reason
 * - Don't ignore potential error cases
 * - Don't ignore just to get 100%
 * - Re-evaluate during debug
 */
