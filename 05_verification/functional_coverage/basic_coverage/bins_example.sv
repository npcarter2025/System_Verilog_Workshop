// ============================================================================
// bins_example.sv - Coverage Bins Definitions and Techniques
// ============================================================================

module bins_example;
    
    // ========================================================================
    // Basic Bins
    // ========================================================================
    
    class basic_bins;
        rand bit [3:0] value;
        
        covergroup cg;
            cp_value: coverpoint value {
                // Single value bin
                bins zero = {0};
                bins one = {1};
                bins max = {15};
                
                // Multiple values in one bin
                bins low = {2, 3, 4, 5};
                
                // Range bin
                bins mid = {[6:10]};
                
                // Remaining values
                bins high = {[11:14]};
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Array of Bins (Automatic Separation)
    // ========================================================================
    
    class array_bins;
        rand bit [3:0] value;
        
        covergroup cg;
            cp_value: coverpoint value {
                // Create separate bin for each value
                bins individual[] = {[0:15]};
                // Results in: individual[0], individual[1], ..., individual[15]
            }
            
            cp_ranges: coverpoint value {
                // Create separate bin for each range value
                bins low_vals[] = {[0:3]};    // low_vals[0], low_vals[1], ...
                bins mid_vals[] = {[4:11]};
                bins high_vals[] = {[12:15]};
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Fixed-Size Array of Bins
    // ========================================================================
    
    class fixed_array_bins;
        rand bit [7:0] value;
        
        covergroup cg;
            cp_value: coverpoint value {
                // Create exactly 4 bins, distributed evenly
                bins quarters[4] = {[0:255]};
                // Results in:
                // quarters[0] = {0-63}
                // quarters[1] = {64-127}
                // quarters[2] = {128-191}
                // quarters[3] = {192-255}
            }
            
            cp_octets: coverpoint value {
                // Create exactly 8 bins
                bins octets[8] = {[0:255]};
                // Each bin covers 32 values
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Default Bin
    // ========================================================================
    
    class default_bin;
        rand bit [7:0] value;
        
        covergroup cg;
            cp_value: coverpoint value {
                bins special = {0, 255};
                bins low = {[1:63]};
                bins high = {[192:254]};
                
                // Catch all other values not covered above
                bins others = default;
                // Covers: {64-191}
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Wildcard Bins
    // ========================================================================
    
    class wildcard_bins;
        rand bit [7:0] opcode;
        
        covergroup cg;
            cp_opcode: coverpoint opcode {
                // Use ? for don't care bits
                wildcard bins arithmetic = {8'b0000_????};  // 0x00-0x0F
                wildcard bins logical    = {8'b0001_????};  // 0x10-0x1F
                wildcard bins shift      = {8'b0010_????};  // 0x20-0x2F
                wildcard bins branch     = {8'b0011_????};  // 0x30-0x3F
                
                // Multiple patterns in one bin
                wildcard bins mem_ops = {8'b0100_????, 8'b0101_????};  // 0x40-0x5F
                
                // Mix wildcard with specific values
                wildcard bins special = {8'b1111_0000, 8'b1111_???1};
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Illegal Bins
    // ========================================================================
    
    class illegal_bins_example;
        rand bit [2:0] mode;
        
        covergroup cg;
            cp_mode: coverpoint mode {
                bins valid[] = {[0:5]};
                
                // These values should never occur
                illegal_bins reserved = {6, 7};
                // Simulator will warn/error if these are sampled
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Ignore Bins
    // ========================================================================
    
    class ignore_bins_example;
        rand bit [3:0] value;
        
        covergroup cg;
            cp_value: coverpoint value {
                bins low = {[0:7]};
                bins high = {[8:15]};
                
                // Don't track these values in coverage
                ignore_bins dont_care = {13, 14};
                // These won't affect coverage percentage
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Bins with Default Sequence
    // ========================================================================
    
    class sequence_bins;
        rand bit [2:0] state;
        bit [2:0] prev_state;
        
        covergroup cg;
            cp_state: coverpoint state {
                bins idle_state = {0};
                bins active_states[] = {[1:6]};
                bins error_state = {7};
            }
            
            // Transition coverage (will be covered more in transition_bins.sv)
            cp_transitions: coverpoint state {
                bins startup = (0 => 1);           // IDLE -> ACTIVE
                bins shutdown = ([1:6] => 0);      // ACTIVE -> IDLE
                bins to_error = ([0:6] => 7);      // Any -> ERROR
            }
        endgroup
        
        function new();
            cg = new();
            prev_state = 0;
        endfunction
        
        function void sample();
            cg.sample();
            prev_state = state;
        endfunction
    endclass
    
    // ========================================================================
    // Bins for Different Data Types
    // ========================================================================
    
    typedef enum bit [1:0] {IDLE, RUN, WAIT, DONE} state_e;
    
    class typed_bins;
        rand bit [7:0] uint_val;
        rand int signed_val;
        rand state_e state;
        rand bit [15:0] addr;
        
        covergroup cg;
            // Unsigned int
            cp_uint: coverpoint uint_val {
                bins zeros = {0};
                bins small = {[1:15]};
                bins medium = {[16:127]};
                bins large = {[128:254]};
                bins max = {255};
            }
            
            // Signed int
            cp_signed: coverpoint signed_val {
                bins negative = {[$:-1]};
                bins zero = {0};
                bins positive = {[1:$]};
            }
            
            // Enum (automatic)
            cp_state: coverpoint state;
            
            // Address with alignment
            cp_addr: coverpoint addr {
                bins aligned = {[0:$]} with (item[1:0] == 2'b00);
                bins unaligned = {[0:$]} with (item[1:0] != 2'b00);
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Bins with Set Operations
    // ========================================================================
    
    class set_operation_bins;
        rand bit [7:0] value;
        
        covergroup cg;
            cp_value: coverpoint value {
                // Intersection
                bins intersection = {[0:100]} intersect {[50:150]};
                // Results in {50-100}
                
                // Union (default behavior for multiple values)
                bins union_vals = {[0:10], [20:30], [40:50]};
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Bins with Conditional Expression (with)
    // ========================================================================
    
    class conditional_bins;
        rand bit [7:0] value;
        
        covergroup cg;
            cp_value: coverpoint value {
                // Only even values
                bins evens = {[0:255]} with (item % 2 == 0);
                
                // Only odd values
                bins odds = {[0:255]} with (item % 2 == 1);
                
                // Powers of 2
                bins pow2 = {[1:255]} with ($countones(item) == 1);
                
                // Values with specific bit pattern
                bins upper_nibble_set = {[0:255]} with (item[7:4] == 4'hF);
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Real-World Example: Memory Transaction
    // ========================================================================
    
    typedef enum bit [1:0] {READ, WRITE, RMW, PREFETCH} mem_op_e;
    
    class memory_transaction_bins;
        rand mem_op_e operation;
        rand bit [31:0] address;
        rand bit [2:0] size;  // 0=byte, 1=half, 2=word, 3=double
        rand bit [7:0] burst_len;
        rand bit cacheable;
        
        covergroup cg;
            // Operation types
            cp_operation: coverpoint operation {
                bins read_op = {READ};
                bins write_op = {WRITE};
                bins rmw_op = {RMW};
                bins prefetch_op = {PREFETCH};
            }
            
            // Address regions
            cp_address: coverpoint address {
                bins low_mem   = {[32'h0000_0000:32'h3FFF_FFFF]};
                bins mid_mem   = {[32'h4000_0000:32'h7FFF_FFFF]};
                bins high_mem  = {[32'h8000_0000:32'hBFFF_FFFF]};
                bins periph    = {[32'hC000_0000:32'hFFFF_FFFF]};
            }
            
            // Address alignment
            cp_alignment: coverpoint address[1:0] {
                bins aligned = {2'b00};
                bins misaligned[] = {2'b01, 2'b10, 2'b11};
            }
            
            // Transfer sizes
            cp_size: coverpoint size {
                bins byte_xfer = {0};
                bins half_xfer = {1};
                bins word_xfer = {2};
                bins dword_xfer = {3};
                illegal_bins invalid = {[4:7]};
            }
            
            // Burst lengths
            cp_burst: coverpoint burst_len {
                bins single = {0};
                bins short_burst = {[1:7]};
                bins medium_burst = {[8:31]};
                bins long_burst = {[32:255]};
            }
            
            // Cacheable flag
            cp_cacheable: coverpoint cacheable {
                bins non_cacheable = {0};
                bins cacheable = {1};
            }
            
            // Power-of-2 burst lengths (common pattern)
            cp_pow2_burst: coverpoint burst_len {
                bins pow2[] = {1, 2, 4, 8, 16, 32, 64, 128};
                bins non_pow2 = default;
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
        
        function void sample();
            cg.sample();
        endfunction
        
        function void print_coverage();
            $display("\n=== Memory Transaction Coverage ===");
            $display("Operation:   %0.2f%%", cg.cp_operation.get_coverage());
            $display("Address:     %0.2f%%", cg.cp_address.get_coverage());
            $display("Alignment:   %0.2f%%", cg.cp_alignment.get_coverage());
            $display("Size:        %0.2f%%", cg.cp_size.get_coverage());
            $display("Burst:       %0.2f%%", cg.cp_burst.get_coverage());
            $display("Cacheable:   %0.2f%%", cg.cp_cacheable.get_coverage());
            $display("Pow2 Burst:  %0.2f%%", cg.cp_pow2_burst.get_coverage());
            $display("Overall:     %0.2f%%", cg.get_coverage());
        endfunction
    endclass
    
    initial begin
        basic_bins basic;
        array_bins arr;
        fixed_array_bins fixed;
        default_bin def;
        wildcard_bins wild;
        conditional_bins cond;
        memory_transaction_bins mem;
        
        $display("=== Bins Examples ===\n");
        
        // Basic bins
        $display("--- Basic Bins ---");
        basic = new();
        repeat(100) begin
            assert(basic.randomize());
            basic.cg.sample();
        end
        $display("Coverage: %0.2f%%", basic.cg.get_coverage());
        
        // Array bins
        $display("\n--- Array Bins (auto-separate) ---");
        arr = new();
        repeat(100) begin
            assert(arr.randomize());
            arr.cg.sample();
        end
        $display("Coverage: %0.2f%%", arr.cg.get_coverage());
        
        // Fixed array bins
        $display("\n--- Fixed Array Bins (4 quarters) ---");
        fixed = new();
        repeat(200) begin
            assert(fixed.randomize());
            fixed.cg.sample();
        end
        $display("Coverage: %0.2f%%", fixed.cg.get_coverage());
        
        // Default bin
        $display("\n--- Default Bin ---");
        def = new();
        repeat(100) begin
            assert(def.randomize());
            def.cg.sample();
        end
        $display("Coverage: %0.2f%%", def.cg.get_coverage());
        
        // Wildcard bins
        $display("\n--- Wildcard Bins ---");
        wild = new();
        repeat(200) begin
            assert(wild.randomize());
            wild.cg.sample();
        end
        $display("Coverage: %0.2f%%", wild.cg.get_coverage());
        
        // Conditional bins
        $display("\n--- Conditional Bins (with clause) ---");
        cond = new();
        repeat(200) begin
            assert(cond.randomize());
            cond.cg.sample();
        end
        $display("Evens: %0.2f%%", cond.cg.cp_value.get_coverage());
        
        // Memory transaction
        $display("\n--- Memory Transaction Example ---");
        mem = new();
        repeat(1000) begin
            assert(mem.randomize());
            mem.sample();
        end
        mem.print_coverage();
    end
    
endmodule

/*
 * BINS SYNTAX AND TYPES:
 * 
 * BASIC BINS:
 *   bins name = {values};
 *   bins name = {[range:range]};
 *   bins name = {val1, val2, [range]};
 * 
 * ARRAY OF BINS:
 *   bins name[] = {[range]};        // Auto-separate
 *   bins name[N] = {[range]};       // Fixed N bins
 * 
 * SPECIAL BINS:
 *   bins name = default;            // Catch remaining values
 *   illegal_bins name = {values};   // Should never occur
 *   ignore_bins name = {values};    // Don't track
 * 
 * WILDCARD BINS:
 *   wildcard bins name = {pattern}; // Use ? for don't care
 * 
 * CONDITIONAL BINS:
 *   bins name = {range} with (item expression);
 *   bins name = {range} intersect {range};
 * 
 * TRANSITION BINS:
 *   bins name = (val1 => val2);     // Sequence
 * 
 * BIN FEATURES:
 * 1. Single or multiple values
 * 2. Ranges with [start:end]
 * 3. Arrays for automatic separation
 * 4. Wildcards for pattern matching
 * 5. Conditionals for filtering
 * 6. Default for catch-all
 * 7. Illegal for error detection
 * 8. Ignore for exclusion
 * 
 * BEST PRACTICES:
 * 1. Name bins meaningfully
 * 2. Cover corner cases explicitly
 * 3. Use illegal_bins for invalid values
 * 4. Use ignore_bins for don't-care values
 * 5. Use array bins for large ranges
 * 6. Group related values together
 * 7. Use wildcard for pattern matching
 * 8. Use conditional bins for complex filtering
 * 
 * COMMON PATTERNS:
 * - Corner cases: {0, max}
 * - Ranges: {[low:mid], [mid:high]}
 * - Powers of 2: {1, 2, 4, 8, 16, ...}
 * - Alignment: with (item[N:0] == 0)
 * - Even/odd: with (item % 2 == 0)
 * - Bit patterns: wildcard bins
 */
