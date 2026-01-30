// ============================================================================
// illegal_bins.sv - Illegal Bins for Error Detection
// ============================================================================

module illegal_bins;
    
    // ========================================================================
    // Basic Illegal Bins
    // ========================================================================
    
    class basic_illegal;
        rand bit [2:0] mode;
        
        covergroup cg;
            cp_mode: coverpoint mode {
                bins valid[] = {[0:5]};
                
                // These values should never occur
                illegal_bins reserved = {6, 7};
                // Simulator will issue warning/error if sampled
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Illegal Range
    // ========================================================================
    
    class illegal_range;
        rand bit [7:0] addr;
        
        covergroup cg;
            cp_addr: coverpoint addr {
                bins valid_low = {[0:127]};
                bins valid_high = {[192:255]};
                
                // Middle range is illegal (protected memory)
                illegal_bins protected_range = {[128:191]};
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Illegal Transitions
    // ========================================================================
    
    typedef enum bit [1:0] {IDLE, ACTIVE, WAIT, ERROR} state_e;
    
    class illegal_transitions;
        state_e state;
        
        covergroup cg;
            cp_state: coverpoint state {
                bins idle = {IDLE};
                bins active = {ACTIVE};
                bins wait_st = {WAIT};
                bins error = {ERROR};
                
                // Valid transitions
                bins idle_to_active = (IDLE => ACTIVE);
                bins active_to_wait = (ACTIVE => WAIT);
                bins wait_to_idle = (WAIT => IDLE);
                bins any_to_error = ([IDLE:WAIT] => ERROR);
                bins error_to_idle = (ERROR => IDLE);
                
                // Illegal: Can't go directly from IDLE to WAIT
                illegal_bins skip_active = (IDLE => WAIT);
                
                // Illegal: Can't stay in ERROR state
                illegal_bins stuck_error = (ERROR[*2]);
                
                // Illegal: Can't go from ERROR to ACTIVE directly
                illegal_bins error_to_active = (ERROR => ACTIVE);
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
    // Illegal Cross Combinations
    // ========================================================================
    
    typedef enum bit [1:0] {READ, WRITE, RMW, PREFETCH} op_e;
    
    class illegal_cross;
        rand op_e operation;
        rand bit [1:0] size;
        rand bit locked;
        
        covergroup cg;
            cp_op: coverpoint operation;
            
            cp_size: coverpoint size {
                bins byte_sz = {0};
                bins half_sz = {1};
                bins word_sz = {2};
                bins dword_sz = {3};
            }
            
            cp_locked: coverpoint locked;
            
            // Cross coverage
            cross_op_size: cross cp_op, cp_size {
                // PREFETCH operations can't be locked
                illegal_bins prefetch_locked = binsof(cp_op.PREFETCH) && 
                                              binsof(cp_size);
                
                // RMW must be word or dword
                illegal_bins rmw_small = binsof(cp_op.RMW) && 
                    (binsof(cp_size.byte_sz) || binsof(cp_size.half_sz));
            }
            
            cross_op_locked: cross cp_op, cp_locked {
                // Only WRITE and RMW can be locked
                illegal_bins read_locked = binsof(cp_op.READ) && 
                                          binsof(cp_locked) intersect {1};
                illegal_bins prefetch_locked2 = binsof(cp_op.PREFETCH) && 
                                                binsof(cp_locked) intersect {1};
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Illegal Wildcard Patterns
    // ========================================================================
    
    class illegal_wildcard;
        rand bit [7:0] opcode;
        
        covergroup cg;
            cp_opcode: coverpoint opcode {
                wildcard bins valid_arithmetic = {8'b0000_????};
                wildcard bins valid_logical = {8'b0001_????};
                wildcard bins valid_shift = {8'b0010_????};
                
                // Reserved opcode patterns
                wildcard illegal_bins reserved1 = {8'b1111_????};
                wildcard illegal_bins reserved2 = {8'b1110_1111};
                
                // Specific illegal opcodes
                illegal_bins illegal_ops = {8'hFF, 8'hFE, 8'hFD};
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Illegal with Conditional (iff)
    // ========================================================================
    
    class illegal_conditional;
        rand bit [7:0] data;
        rand bit debug_mode;
        rand bit production_mode;
        
        covergroup cg;
            // In production mode, certain values are illegal
            cp_prod: coverpoint data iff (production_mode && !debug_mode) {
                bins normal_data = {[1:254]};
                
                // Reserved values in production
                illegal_bins prod_reserved = {0, 255};
            }
            
            // In debug mode, all values allowed
            cp_debug: coverpoint data iff (debug_mode) {
                bins all_values[] = {[0:255]};
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Protocol Illegal Combinations
    // ========================================================================
    
    typedef enum bit [1:0] {FIXED, INCR, WRAP, RESERVED} burst_e;
    
    class protocol_illegal;
        rand burst_e burst_type;
        rand bit [7:0] burst_len;
        rand bit [2:0] burst_size;
        rand bit [31:0] addr;
        
        covergroup cg;
            cp_burst: coverpoint burst_type {
                bins fixed = {FIXED};
                bins incr = {INCR};
                bins wrap = {WRAP};
                
                // RESERVED burst type is illegal
                illegal_bins reserved = {RESERVED};
            }
            
            cp_len: coverpoint burst_len {
                bins short_burst = {[0:7]};
                bins medium_burst = {[8:31]};
                bins long_burst = {[32:255]};
            }
            
            cp_addr_align: coverpoint addr[1:0] {
                bins aligned = {2'b00};
                bins unaligned = {2'b01, 2'b10, 2'b11};
            }
            
            // WRAP burst constraints
            cross_burst_len: cross cp_burst, cp_len {
                // WRAP only valid with lengths 1, 3, 7, 15 (2, 4, 8, 16 beats)
                illegal_bins wrap_invalid_len = binsof(cp_burst.WRAP) && 
                    !binsof(cp_len) intersect {1, 3, 7, 15};
            }
            
            // Alignment constraints for WRAP
            cross_burst_align: cross cp_burst, cp_addr_align {
                // WRAP bursts must be aligned
                illegal_bins wrap_unaligned = binsof(cp_burst.WRAP) && 
                                             binsof(cp_addr_align.unaligned);
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Illegal Combinations Based on Mode
    // ========================================================================
    
    class mode_based_illegal;
        rand bit [1:0] mode;
        rand bit [3:0] config;
        rand bit enable;
        rand bit turbo;
        
        covergroup cg;
            cp_mode: coverpoint mode {
                bins safe_mode = {0};
                bins normal_mode = {1};
                bins turbo_mode = {2};
                bins test_mode = {3};
            }
            
            cp_config: coverpoint config;
            cp_enable: coverpoint enable;
            cp_turbo: coverpoint turbo;
            
            // Mode-specific illegal combinations
            cross_mode_config: cross cp_mode, cp_config {
                // Config 15 illegal in safe mode
                illegal_bins safe_high_config = binsof(cp_mode.safe_mode) && 
                    binsof(cp_config) intersect {15};
                
                // Config 0 illegal in turbo mode
                illegal_bins turbo_no_config = binsof(cp_mode.turbo_mode) && 
                    binsof(cp_config) intersect {0};
            }
            
            cross_mode_enable: cross cp_mode, cp_enable {
                // Must be enabled in turbo mode
                illegal_bins turbo_disabled = binsof(cp_mode.turbo_mode) && 
                    binsof(cp_enable) intersect {0};
                
                // Can't be enabled in test mode
                illegal_bins test_enabled = binsof(cp_mode.test_mode) && 
                    binsof(cp_enable) intersect {1};
            }
            
            cross_mode_turbo: cross cp_mode, cp_turbo {
                // Turbo flag only valid in turbo mode
                illegal_bins turbo_wrong_mode = !binsof(cp_mode.turbo_mode) && 
                    binsof(cp_turbo) intersect {1};
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Real-World: AXI Illegal Scenarios
    // ========================================================================
    
    typedef enum bit [1:0] {AXI_OKAY, AXI_EXOKAY, AXI_SLVERR, AXI_DECERR} resp_e;
    
    class axi_illegal;
        rand bit [2:0] size;
        rand bit [7:0] len;
        rand burst_e burst;
        rand bit [31:0] addr;
        rand bit exclusive;
        rand resp_e resp;
        rand bit write;
        
        covergroup cg;
            cp_size: coverpoint size {
                bins byte_sz = {0};
                bins half_sz = {1};
                bins word_sz = {2};
                bins dword_sz = {3};
                illegal_bins invalid_size = {[4:7]};
            }
            
            cp_len: coverpoint len;
            cp_burst: coverpoint burst;
            cp_exclusive: coverpoint exclusive;
            cp_resp: coverpoint resp;
            cp_write: coverpoint write;
            
            // Address alignment based on size
            cp_addr_low: coverpoint addr[2:0] {
                bins aligned_byte = {3'b000, 3'b001, 3'b010, 3'b011, 
                                    3'b100, 3'b101, 3'b110, 3'b111};
                bins aligned_half = {3'b000, 3'b010, 3'b100, 3'b110};
                bins aligned_word = {3'b000, 3'b100};
                bins aligned_dword = {3'b000};
            }
            
            // Size vs alignment
            cross_size_align: cross cp_size, cp_addr_low {
                // Half-word must be 2-byte aligned
                illegal_bins half_unaligned = binsof(cp_size.half_sz) && 
                    !binsof(cp_addr_low.aligned_half);
                
                // Word must be 4-byte aligned
                illegal_bins word_unaligned = binsof(cp_size.word_sz) && 
                    !binsof(cp_addr_low.aligned_word);
                
                // Double-word must be 8-byte aligned
                illegal_bins dword_unaligned = binsof(cp_size.dword_sz) && 
                    !binsof(cp_addr_low.aligned_dword);
            }
            
            // WRAP burst constraints
            cross_burst_len_wrap: cross cp_burst, cp_len {
                illegal_bins wrap_bad_len = binsof(cp_burst.WRAP) && 
                    !binsof(cp_len) intersect {1, 3, 7, 15, 31, 63, 127, 255};
            }
            
            // Exclusive access response
            cross_excl_resp: cross cp_exclusive, cp_resp {
                // Can't have EXOKAY without exclusive access
                illegal_bins exokay_no_excl = binsof(cp_exclusive) intersect {0} && 
                    binsof(cp_resp.AXI_EXOKAY);
            }
            
            // 4KB boundary crossing
            // (Simplified - real check needs address + transfer size)
            cp_boundary: coverpoint addr[11:0] {
                bins safe = {[0:4000]};
                bins near_boundary = {[4001:4095]};
            }
            
            cross_boundary_size: cross cp_boundary, cp_size, cp_len {
                // Large transfers near boundary are risky
                // (Real implementation would calculate exact crossing)
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
        
        function void sample();
            cg.sample();
        endfunction
        
        function void check_illegal();
            // Runtime checks for illegal scenarios
            if (burst == RESERVED) begin
                $error("Illegal: RESERVED burst type sampled!");
            end
            
            if (burst == WRAP && !(len inside {1, 3, 7, 15})) begin
                $error("Illegal: WRAP burst with invalid length %0d", len+1);
            end
            
            if (size == 1 && addr[0] != 0) begin
                $error("Illegal: Half-word transfer unaligned at 0x%0h", addr);
            end
            
            if (size == 2 && addr[1:0] != 0) begin
                $error("Illegal: Word transfer unaligned at 0x%0h", addr);
            end
        endfunction
    endclass
    
    initial begin
        basic_illegal basic;
        illegal_range range;
        illegal_transitions trans;
        illegal_cross xcross;
        protocol_illegal proto;
        axi_illegal axi;
        
        $display("=== Illegal Bins Examples ===\n");
        
        // Basic
        $display("--- Basic Illegal Bins ---");
        basic = new();
        repeat(100) begin
            basic.mode = $urandom_range(0, 5);  // Only generate valid values
            basic.cg.sample();
        end
        $display("Coverage: %0.2f%%", basic.cg.get_coverage());
        // Try illegal value (should warn)
        $display("Sampling illegal value 7...");
        basic.mode = 7;
        basic.cg.sample();
        
        // Transitions
        $display("\n--- Illegal Transitions ---");
        trans = new();
        trans.next(IDLE);
        trans.next(ACTIVE);
        trans.next(WAIT);
        trans.next(IDLE);
        $display("Valid sequence completed");
        
        // Try illegal transition
        $display("Attempting illegal transition IDLE->WAIT...");
        trans.next(IDLE);
        trans.next(WAIT);  // Should warn
        
        // Protocol
        $display("\n--- Protocol Illegal Combinations ---");
        proto = new();
        repeat(200) begin
            assert(proto.randomize() with {
                burst_type != RESERVED;
                (burst_type == WRAP) -> (burst_len inside {1, 3, 7, 15});
                (burst_type == WRAP) -> (addr[1:0] == 2'b00);
            });
            proto.cg.sample();
        end
        $display("Coverage: %0.2f%%", proto.cg.get_coverage());
        
        // AXI
        $display("\n--- AXI Illegal Scenarios ---");
        axi = new();
        repeat(500) begin
            assert(axi.randomize() with {
                size inside {[0:3]};
                burst != RESERVED;
                (burst == WRAP) -> (len inside {1, 3, 7, 15});
                (size == 1) -> (addr[0] == 0);
                (size == 2) -> (addr[1:0] == 2'b00);
                (size == 3) -> (addr[2:0] == 3'b000);
                (!exclusive) -> (resp != AXI_EXOKAY);
            });
            axi.sample();
        end
        $display("Coverage: %0.2f%%", axi.cg.get_coverage());
    end
    
endmodule

/*
 * ILLEGAL_BINS SYNTAX:
 * 
 * BASIC:
 *   illegal_bins name = {values};
 * 
 * RANGE:
 *   illegal_bins name = {[start:end]};
 * 
 * WILDCARD:
 *   wildcard illegal_bins name = {pattern};
 * 
 * TRANSITIONS:
 *   illegal_bins name = (val1 => val2);
 * 
 * IN CROSS:
 *   illegal_bins name = binsof(cp1.bin1) && binsof(cp2.bin2);
 * 
 * PURPOSE:
 * 1. Detect illegal/unexpected values
 * 2. Catch design bugs
 * 3. Verify constraints are working
 * 4. Document invalid combinations
 * 5. Runtime error detection
 * 
 * BEHAVIOR:
 * - When illegal bin is hit, simulator issues warning/error
 * - Coverage tools flag as illegal hit
 * - Does NOT affect coverage percentage
 * - Used for error detection, not coverage measurement
 * 
 * DIFFERENCE FROM IGNORE_BINS:
 * - illegal_bins: Should NEVER occur (error if seen)
 * - ignore_bins: Can occur, just don't track (neutral)
 * 
 * WHEN TO USE:
 * - Reserved values/opcodes
 * - Invalid state transitions
 * - Protocol violations
 * - Impossible combinations
 * - Out-of-spec conditions
 * - Constraint violations
 * 
 * BEST PRACTICES:
 * 1. Document WHY value is illegal
 * 2. Use for protocol compliance checking
 * 3. Combine with assertions for robust checking
 * 4. Check coverage reports for illegal hits
 * 5. Use in cross coverage for invalid combinations
 * 6. Add runtime checks in addition to coverage
 * 
 * COMMON PATTERNS:
 * - Reserved opcodes: illegal_bins reserved = {[high:max]};
 * - Invalid states: illegal_bins bad_state = (A => B);
 * - Misaligned: illegal_bins unaligned = {addr} with (item[1:0] != 0);
 * - Illegal combos: illegal_bins = binsof(a) && binsof(b);
 * 
 * DEBUGGING:
 * - If illegal bin hit, check:
 *   1. Is it really illegal?
 *   2. Bug in DUT?
 *   3. Bug in testbench?
 *   4. Missing constraint?
 *   5. Wrong assumption?
 */
