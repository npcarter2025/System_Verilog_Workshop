// ============================================================================
// coverpoint.sv - Coverpoint Expressions and Techniques
// ============================================================================

module coverpoint;
    
    // ========================================================================
    // Simple Coverpoint
    // ========================================================================
    
    class simple_coverpoint_example;
        rand bit [3:0] value;
        
        covergroup cg;
            // Automatic bins (one per value)
            cp_value: coverpoint value;
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Coverpoint with Expressions
    // ========================================================================
    
    class expression_coverpoint;
        rand bit [7:0] a;
        rand bit [7:0] b;
        
        covergroup cg;
            // Cover sum
            cp_sum: coverpoint (a + b);
            
            // Cover difference
            cp_diff: coverpoint (a - b);
            
            // Cover max
            cp_max: coverpoint (a > b ? a : b);
            
            // Cover bit operations
            cp_and: coverpoint (a & b);
            cp_or: coverpoint (a | b);
            cp_xor: coverpoint (a ^ b);
            
            // Cover comparison result
            cp_equal: coverpoint (a == b);
            cp_greater: coverpoint (a > b);
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Coverpoint with Bins
    // ========================================================================
    
    class bins_coverpoint;
        rand bit [7:0] addr;
        
        covergroup cg;
            cp_addr: coverpoint addr {
                // Single value bins
                bins zero = {0};
                bins max = {255};
                
                // Range bins
                bins low = {[1:63]};
                bins mid = {[64:191]};
                bins high = {[192:254]};
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Coverpoint Options
    // ========================================================================
    
    class coverpoint_options;
        rand bit [7:0] data;
        
        covergroup cg;
            cp_data: coverpoint data {
                // Coverpoint-specific options
                option.weight = 5;           // Higher weight in coverage calculation
                option.goal = 90;            // 90% goal for this coverpoint
                option.at_least = 3;         // At least 3 hits per bin
                option.auto_bin_max = 16;    // Max automatic bins
                
                bins values[] = {[0:255]};   // Will create up to 16 bins
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Enum Coverpoint
    // ========================================================================
    
    typedef enum bit [1:0] {IDLE, READ, WRITE, ERROR} state_e;
    
    class enum_coverpoint;
        rand state_e state;
        
        covergroup cg;
            // Automatic bins for each enum value
            cp_state: coverpoint state;
            
            // Explicit bins for enum
            cp_state_explicit: coverpoint state {
                bins idle_bin = {IDLE};
                bins read_bin = {READ};
                bins write_bin = {WRITE};
                bins error_bin = {ERROR};
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Boolean Coverpoint
    // ========================================================================
    
    class boolean_coverpoint;
        rand bit enable;
        rand bit ready;
        rand bit valid;
        
        covergroup cg;
            // Simple boolean coverage
            cp_enable: coverpoint enable {
                bins off = {0};
                bins on = {1};
            }
            
            // Multiple booleans
            cp_ready: coverpoint ready;
            cp_valid: coverpoint valid;
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Bit-Field Coverpoint
    // ========================================================================
    
    class bitfield_coverpoint;
        rand bit [7:0] flags;
        
        covergroup cg;
            // Cover individual bit
            cp_bit0: coverpoint flags[0];
            cp_bit7: coverpoint flags[7];
            
            // Cover bit slice
            cp_lower_nibble: coverpoint flags[3:0];
            cp_upper_nibble: coverpoint flags[7:4];
            
            // Cover number of set bits
            cp_popcount: coverpoint $countones(flags) {
                bins none = {0};
                bins few = {[1:3]};
                bins some = {[4:5]};
                bins many = {[6:8]};
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Conditional Coverpoint (iff)
    // ========================================================================
    
    class conditional_coverpoint;
        rand bit [7:0] data;
        rand bit valid;
        rand bit enable;
        
        covergroup cg;
            // Only sample when valid
            cp_data_when_valid: coverpoint data iff (valid);
            
            // Only sample when both valid and enable
            cp_data_enabled: coverpoint data iff (valid && enable);
            
            // Sample when not in reset (example)
            cp_always: coverpoint data;
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Wildcard Coverpoint
    // ========================================================================
    
    class wildcard_coverpoint;
        rand bit [7:0] opcode;
        
        covergroup cg;
            cp_opcode: coverpoint opcode {
                // Wildcard bins (? = don't care)
                wildcard bins load_ops  = {8'b0000_????};  // 0x00-0x0F
                wildcard bins store_ops = {8'b0001_????};  // 0x10-0x1F
                wildcard bins alu_ops   = {8'b0010_????};  // 0x20-0x2F
                wildcard bins branch_ops = {8'b0011_????}; // 0x30-0x3F
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Multi-Dimensional Array Coverpoint
    // ========================================================================
    
    class array_coverpoint;
        rand bit [3:0] arr[4];
        
        covergroup cg;
            // Cover each array element
            cp_arr0: coverpoint arr[0];
            cp_arr1: coverpoint arr[1];
            cp_arr2: coverpoint arr[2];
            cp_arr3: coverpoint arr[3];
            
            // Cover array sum
            cp_sum: coverpoint (arr[0] + arr[1] + arr[2] + arr[3]);
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Coverpoint Label and Bins Count
    // ========================================================================
    
    class labeled_coverpoint;
        rand bit [7:0] value;
        
        covergroup cg;
            cp_value: coverpoint value {
                // Use labels for documentation
                bins corner_low = {0, 1, 2};
                bins corner_high = {253, 254, 255};
                bins middle[] = {[3:252]};  // Array of bins
            }
        endgroup
        
        function new();
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Real-World: AXI Transaction Coverpoint
    // ========================================================================
    
    typedef enum bit [1:0] {FIXED, INCR, WRAP, RESERVED} burst_e;
    typedef enum bit [2:0] {OKAY, EXOKAY, SLVERR, DECERR} resp_e;
    
    class axi_coverpoint;
        rand bit [31:0] addr;
        rand bit [7:0] len;
        rand bit [2:0] size;
        rand burst_e burst;
        rand resp_e resp;
        rand bit write;
        
        covergroup cg;
            // Address alignment
            cp_addr_align: coverpoint addr[1:0] {
                bins aligned = {2'b00};
                bins unaligned[] = {2'b01, 2'b10, 2'b11};
            }
            
            // Transfer size
            cp_size: coverpoint size {
                bins byte_transfer = {0};
                bins half_transfer = {1};
                bins word_transfer = {2};
                bins dword_transfer = {3};
            }
            
            // Burst length categories
            cp_len: coverpoint len {
                bins single = {0};
                bins short_burst = {[1:7]};
                bins medium_burst = {[8:15]};
                bins long_burst = {[16:255]};
            }
            
            // Burst type
            cp_burst: coverpoint burst {
                bins fixed = {FIXED};
                bins incr = {INCR};
                bins wrap = {WRAP};
                illegal_bins reserved = {RESERVED};
            }
            
            // Response
            cp_resp: coverpoint resp {
                bins okay = {OKAY};
                bins exclusive = {EXOKAY};
                bins slave_error = {SLVERR};
                bins decode_error = {DECERR};
            }
            
            // Write vs Read
            cp_write: coverpoint write {
                bins read = {0};
                bins write = {1};
            }
            
            // Only sample valid bursts
            cp_valid_len: coverpoint len iff (burst != RESERVED);
        endgroup
        
        function new();
            cg = new();
        endfunction
        
        function void sample();
            cg.sample();
        endfunction
    endclass
    
    initial begin
        simple_coverpoint_example simple;
        expression_coverpoint expr;
        bins_coverpoint bins;
        coverpoint_options opts;
        enum_coverpoint enum_cp;
        boolean_coverpoint bool_cp;
        bitfield_coverpoint bitfield;
        conditional_coverpoint cond;
        wildcard_coverpoint wildcard;
        axi_coverpoint axi;
        
        $display("=== Coverpoint Examples ===\n");
        
        // Simple
        $display("--- Simple Coverpoint (4-bit, 16 bins) ---");
        simple = new();
        repeat(50) begin
            assert(simple.randomize());
            simple.cg.sample();
        end
        $display("Coverage: %0.2f%%", simple.cg.get_coverage());
        
        // Expression
        $display("\n--- Expression Coverpoint ---");
        expr = new();
        repeat(100) begin
            assert(expr.randomize());
            expr.cg.sample();
        end
        $display("Sum coverage: %0.2f%%", expr.cg.cp_sum.get_coverage());
        $display("Equal coverage: %0.2f%%", expr.cg.cp_equal.get_coverage());
        
        // Bins
        $display("\n--- Coverpoint with Bins ---");
        bins = new();
        repeat(100) begin
            assert(bins.randomize());
            bins.cg.sample();
        end
        $display("Coverage: %0.2f%%", bins.cg.get_coverage());
        
        // Enum
        $display("\n--- Enum Coverpoint ---");
        enum_cp = new();
        repeat(50) begin
            assert(enum_cp.randomize());
            enum_cp.cg.sample();
        end
        $display("Coverage: %0.2f%%", enum_cp.cg.get_coverage());
        
        // Boolean
        $display("\n--- Boolean Coverpoint ---");
        bool_cp = new();
        repeat(20) begin
            assert(bool_cp.randomize());
            bool_cp.cg.sample();
        end
        $display("Coverage: %0.2f%%", bool_cp.cg.get_coverage());
        
        // Bitfield
        $display("\n--- Bitfield Coverpoint ---");
        bitfield = new();
        repeat(100) begin
            assert(bitfield.randomize());
            bitfield.cg.sample();
        end
        $display("Popcount coverage: %0.2f%%", bitfield.cg.cp_popcount.get_coverage());
        
        // Conditional
        $display("\n--- Conditional Coverpoint (iff) ---");
        cond = new();
        repeat(100) begin
            assert(cond.randomize());
            cond.cg.sample();
        end
        $display("Always coverage: %0.2f%%", cond.cg.cp_always.get_coverage());
        $display("When valid coverage: %0.2f%%", cond.cg.cp_data_when_valid.get_coverage());
        
        // Wildcard
        $display("\n--- Wildcard Coverpoint ---");
        wildcard = new();
        repeat(200) begin
            assert(wildcard.randomize());
            wildcard.cg.sample();
        end
        $display("Coverage: %0.2f%%", wildcard.cg.get_coverage());
        
        // AXI
        $display("\n--- AXI Transaction Coverpoint ---");
        axi = new();
        repeat(500) begin
            assert(axi.randomize());
            axi.sample();
        end
        $display("Address alignment: %0.2f%%", axi.cg.cp_addr_align.get_coverage());
        $display("Size coverage: %0.2f%%", axi.cg.cp_size.get_coverage());
        $display("Burst type: %0.2f%%", axi.cg.cp_burst.get_coverage());
        $display("Response: %0.2f%%", axi.cg.cp_resp.get_coverage());
        $display("Overall: %0.2f%%", axi.cg.get_coverage());
    end
    
endmodule

/*
 * COVERPOINT SYNTAX:
 * 
 * BASIC:
 *   coverpoint variable;
 * 
 * WITH EXPRESSION:
 *   coverpoint (a + b);
 * 
 * WITH BINS:
 *   coverpoint var {
 *     bins name = {values};
 *   }
 * 
 * WITH CONDITION:
 *   coverpoint var iff (condition);
 * 
 * COVERPOINT FEATURES:
 * 1. Automatic bins (one per unique value)
 * 2. User-defined bins (ranges, wildcards)
 * 3. Expressions (arithmetic, logical, ternary)
 * 4. Conditional sampling (iff)
 * 5. Options (weight, goal, at_least)
 * 
 * COVERPOINT OPTIONS:
 * - option.weight: Relative importance
 * - option.goal: Target percentage
 * - option.at_least: Min hits per bin
 * - option.auto_bin_max: Max automatic bins
 * 
 * COMMON PATTERNS:
 * - Enum: One bin per enum value
 * - Boolean: 0 and 1 bins
 * - Range: Group values into meaningful ranges
 * - Wildcard: Pattern matching with ?
 * - Conditional: iff for valid-only sampling
 * 
 * BEST PRACTICES:
 * 1. Name coverpoints descriptively (cp_*)
 * 2. Group related values into bins
 * 3. Use iff to avoid sampling invalid states
 * 4. Use wildcard for pattern matching
 * 5. Set auto_bin_max for large ranges
 * 6. Use expressions for derived values
 * 
 * WHAT TO COVER:
 * - Input values (all possible inputs)
 * - Output values (responses, errors)
 * - State transitions
 * - Edge cases (0, max, boundaries)
 * - Error conditions
 */
