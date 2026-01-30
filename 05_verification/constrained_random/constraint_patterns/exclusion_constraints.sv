// ============================================================================
// exclusion_constraints.sv - Exclusion and Negative Constraint Patterns
// ============================================================================

module exclusion_constraints;
    
    // ========================================================================
    // Basic Exclusions
    // ========================================================================
    
    class basic_exclusions;
        rand bit [7:0] value;
        
        // Exclude specific values
        constraint exclude_c {
            !(value inside {0, 255});  // Not 0 or 255
        }
        
        // Alternative syntax
        constraint exclude_alt_c {
            value != 42;
            value != 13;
        }
    endclass
    
    // ========================================================================
    // Reserved Address Ranges
    // ========================================================================
    
    class address_with_exclusions;
        rand bit [31:0] addr;
        
        // Exclude reserved/protected ranges
        constraint exclude_reserved_c {
            !(addr inside {[32'h0000_0000:32'h0000_0FFF]});  // Boot ROM
            !(addr inside {[32'hFFFF_0000:32'hFFFF_FFFF]});  // System registers
            !(addr inside {[32'h8000_0000:32'h8FFF_FFFF]});  // Peripheral space
        }
        
        // Alternative: only allow specific ranges
        constraint allow_ranges_c {
            addr inside {
                [32'h1000_0000:32'h1FFF_FFFF],  // DRAM
                [32'h2000_0000:32'h2FFF_FFFF],  // SRAM
                [32'h4000_0000:32'h4FFF_FFFF]   // External memory
            };
        }
    endclass
    
    // ========================================================================
    // Illegal Combinations
    // ========================================================================
    
    class illegal_combinations;
        rand bit [1:0] mode;
        rand bit [2:0] config;
        rand bit       enable;
        
        // Exclude invalid mode+config combinations
        constraint no_illegal_combo_c {
            !(mode == 2'b00 && config == 3'b111);  // Reserved
            !(mode == 2'b11 && config == 3'b000);  // Invalid
            !(mode == 2'b01 && enable == 1'b0);    // Mode 1 requires enable
        }
    endclass
    
    // ========================================================================
    // Hazard Avoidance
    // ========================================================================
    
    class hazard_free_sequence;
        rand bit [3:0] reg_addr;
        rand bit [3:0] prev_reg_addr;  // From previous transaction
        rand bit       write;
        rand bit       prev_write;
        
        // Read-after-write hazard: don't read same register just written
        constraint no_raw_hazard_c {
            !(write == 0 && prev_write == 1 && reg_addr == prev_reg_addr);
        }
        
        // Write-after-write: avoid writing same register twice in a row
        constraint no_waw_c {
            !(write == 1 && prev_write == 1 && reg_addr == prev_reg_addr);
        }
    endclass
    
    // ========================================================================
    // Boundary Cases
    // ========================================================================
    
    class boundary_exclusions;
        rand bit [31:0] addr;
        rand bit [15:0] size;
        
        // Exclude crossing 4KB boundary
        constraint no_4kb_cross_c {
            ((addr / 4096) == ((addr + size - 1) / 4096));
        }
        
        // Exclude page boundaries
        constraint no_page_boundary_c {
            !((addr[11:0] + size) > 12'h1000);
        }
        
        // Exclude wraparound
        constraint no_wraparound_c {
            (addr + size) > addr;  // No overflow
        }
    endclass
    
    // ========================================================================
    // Error Injection Control
    // ========================================================================
    
    class controlled_error_injection;
        rand bit [7:0] data;
        rand bit       inject_error;
        rand bit [2:0] error_type;
        
        real error_rate;  // 0.0 - 1.0
        
        function new(real rate = 0.01);
            error_rate = rate;
        endfunction
        
        // Controlled error injection rate
        constraint error_inject_c {
            inject_error dist {
                1'b0 := int'((1.0 - error_rate) * 100),
                1'b1 := int'(error_rate * 100)
            };
        }
        
        // Most of the time, no errors
        constraint mostly_good_c {
            !inject_error -> {
                // Normal data constraints
                data inside {[1:254]};
            }
        }
        
        // When injecting errors, specific patterns
        constraint error_data_c {
            inject_error -> {
                error_type inside {[0:7]};
                
                (error_type == 0) -> (data == 8'h00);      // All zeros
                (error_type == 1) -> (data == 8'hFF);      // All ones
                (error_type == 2) -> ($countones(data) == 1); // Single bit
                (error_type == 3) -> (data[7] != data[6]); // Bit flip
            }
        }
    endclass
    
    // ========================================================================
    // Priority-Based Exclusions
    // ========================================================================
    
    class priority_exclusions;
        rand bit [1:0] priority;
        rand bit [7:0] id;
        
        // High priority IDs (0-15)
        // Medium priority IDs (16-127)
        // Low priority IDs (128-255)
        constraint priority_id_c {
            (priority == 2'b11) -> (id inside {[0:15]});
            (priority == 2'b10) -> (id inside {[16:127]});
            (priority == 2'b01) -> (id inside {[128:255]});
            // Priority 0 excluded
            priority != 2'b00;
        }
    endclass
    
    // ========================================================================
    // State-Dependent Exclusions
    // ========================================================================
    
    class state_aware_constraints;
        typedef enum bit [1:0] {
            IDLE   = 2'b00,
            ACTIVE = 2'b01,
            WAIT   = 2'b10,
            ERROR  = 2'b11
        } state_e;
        
        rand state_e current_state;
        rand state_e next_state;
        rand bit [7:0] data;
        
        // State transition exclusions
        constraint valid_transitions_c {
            // Can't go from ERROR directly to ACTIVE
            !(current_state == ERROR && next_state == ACTIVE);
            
            // Can't stay in WAIT
            !(current_state == WAIT && next_state == WAIT);
            
            // Must go through IDLE from ERROR
            (current_state == ERROR) -> (next_state == IDLE);
        }
        
        // State-dependent data constraints
        constraint state_data_c {
            (current_state == IDLE)   -> (data == 8'h00);
            (current_state == ERROR)  -> (data == 8'hFF);
            (current_state == ACTIVE) -> (data inside {[1:254]});
        }
    endclass
    
    // ========================================================================
    // Uniqueness Constraints
    // ========================================================================
    
    class unique_values;
        rand bit [7:0] values[10];
        
        // All values must be unique (exclude duplicates)
        constraint all_unique_c {
            foreach(values[i])
                foreach(values[j])
                    (i != j) -> (values[i] != values[j]);
        }
        
        // Exclude certain values entirely
        constraint exclude_values_c {
            foreach(values[i])
                !(values[i] inside {0, 255});
        }
    endclass
    
    // ========================================================================
    // Conditional Exclusions
    // ========================================================================
    
    class conditional_exclusions;
        rand bit [15:0] addr;
        rand bit [7:0] data;
        rand bit debug_mode;
        rand bit test_mode;
        
        // Exclude certain addresses in production mode
        constraint production_exclusions_c {
            (!debug_mode && !test_mode) -> {
                !(addr inside {[16'h8000:16'h8FFF]});  // Debug registers
                !(addr inside {[16'h9000:16'h9FFF]});  // Test registers
            }
        }
        
        // In test mode, exclude production addresses
        constraint test_exclusions_c {
            test_mode -> {
                !(addr inside {[16'h0000:16'h7FFF]});  // Production space
            }
        }
        
        // Data restrictions in non-debug mode
        constraint data_exclusions_c {
            !debug_mode -> {
                data != 8'h00;  // Reserved
                data != 8'hFF;  // Reserved
            }
        }
    endclass
    
    initial begin
        basic_exclusions basic;
        address_with_exclusions addr_excl;
        illegal_combinations illegal;
        hazard_free_sequence hazard;
        boundary_exclusions boundary;
        controlled_error_injection error_inj;
        priority_exclusions priority;
        state_aware_constraints state;
        unique_values unique;
        conditional_exclusions conditional;
        
        $display("=== Exclusion Constraint Patterns ===\n");
        
        // Basic
        $display("--- Basic Exclusions (not 0, 13, 42, 255) ---");
        basic = new();
        repeat(10) begin
            assert(basic.randomize());
            $display("%0d", basic.value);
        end
        
        // Address exclusions
        $display("\n--- Address Exclusions ---");
        addr_excl = new();
        repeat(5) begin
            assert(addr_excl.randomize());
            $display("0x%08h", addr_excl.addr);
        end
        
        // Illegal combinations
        $display("\n--- Illegal Combination Avoidance ---");
        illegal = new();
        repeat(10) begin
            assert(illegal.randomize());
            $display("mode=%0d, config=%0d, enable=%0b",
                    illegal.mode, illegal.config, illegal.enable);
        end
        
        // Hazard-free
        $display("\n--- Hazard-Free Sequences ---");
        hazard = new();
        hazard.prev_reg_addr = 4'h5;
        hazard.prev_write = 1;
        repeat(5) begin
            assert(hazard.randomize());
            $display("prev: r%0d(%s), curr: r%0d(%s)",
                    hazard.prev_reg_addr, hazard.prev_write ? "W" : "R",
                    hazard.reg_addr, hazard.write ? "W" : "R");
            hazard.prev_reg_addr = hazard.reg_addr;
            hazard.prev_write = hazard.write;
        end
        
        // Boundary exclusions
        $display("\n--- Boundary Exclusions ---");
        boundary = new();
        repeat(5) begin
            assert(boundary.randomize());
            $display("addr=0x%08h, size=%0d, end=0x%08h (page=%0d)",
                    boundary.addr, boundary.size,
                    boundary.addr + boundary.size - 1,
                    boundary.addr / 4096);
        end
        
        // Error injection
        $display("\n--- Controlled Error Injection (1%%) ---");
        error_inj = new(0.01);
        repeat(20) begin
            assert(error_inj.randomize());
            if (error_inj.inject_error)
                $display("ERROR: data=0x%02h, type=%0d", error_inj.data, error_inj.error_type);
        end
        
        // Priority
        $display("\n--- Priority-Based Exclusions ---");
        priority = new();
        repeat(10) begin
            assert(priority.randomize());
            $display("priority=%0d, id=%0d", priority.priority, priority.id);
        end
        
        // State-aware
        $display("\n--- State-Dependent Exclusions ---");
        state = new();
        state.current_state = state.IDLE;
        repeat(10) begin
            assert(state.randomize());
            $display("%s -> %s (data=0x%02h)",
                    state.current_state.name(), state.next_state.name(), state.data);
            state.current_state = state.next_state;
        end
        
        // Unique values
        $display("\n--- Unique Values ---");
        unique = new();
        assert(unique.randomize());
        $write("Values: ");
        foreach(unique.values[i]) $write("%0d ", unique.values[i]);
        $display("");
        
        // Conditional
        $display("\n--- Conditional Exclusions ---");
        conditional = new();
        conditional.debug_mode = 0;
        conditional.test_mode = 0;
        $display("Production mode:");
        repeat(3) begin
            assert(conditional.randomize());
            $display("  addr=0x%04h, data=0x%02h", conditional.addr, conditional.data);
        end
        
        conditional.test_mode = 1;
        $display("Test mode:");
        repeat(3) begin
            assert(conditional.randomize());
            $display("  addr=0x%04h, data=0x%02h", conditional.addr, conditional.data);
        end
    end
    
endmodule

/*
 * EXCLUSION CONSTRAINT PATTERNS:
 * 
 * COMMON EXCLUSION TYPES:
 * 1. Reserved values (0, -1, special codes)
 * 2. Protected address ranges
 * 3. Illegal state combinations
 * 4. Hazardous sequences
 * 5. Boundary violations
 * 
 * SYNTAX OPTIONS:
 * - Negation: !(expr)
 * - Not equal: var != value
 * - Not inside: !(var inside {...})
 * - Implication: condition -> (exclusion)
 * 
 * USE CASES:
 * - Safety: Avoid dangerous operations
 * - Correctness: Exclude invalid combinations
 * - Performance: Avoid known bad patterns
 * - Testing: Control error injection
 * 
 * BEST PRACTICES:
 * - Document WHY values are excluded
 * - Use positive constraints when possible
 * - Group related exclusions together
 * - Make exclusions conditional when appropriate
 * - Test that exclusions work (no excluded values generated)
 * 
 * ANTI-PATTERNS:
 * ❌ Over-constraining (excluding too much)
 * ❌ Circular exclusions (nothing left to choose)
 * ❌ Undocumented magic numbers
 * ✅ Clear, justified exclusions
 * ✅ Maintainable constraint structure
 */
