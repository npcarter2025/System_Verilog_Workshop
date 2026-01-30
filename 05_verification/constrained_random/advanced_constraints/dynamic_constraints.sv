// ============================================================================
// dynamic_constraints.sv - Dynamic Constraint Control (constraint_mode)
// ============================================================================

module dynamic_constraints;
    
    class flexible_packet;
        rand bit [7:0] addr;
        rand bit [31:0] data;
        rand bit [1:0] priority;
        
        // Constraint 1: Address range
        constraint addr_low_c {
            addr inside {[0:63]};
        }
        
        constraint addr_high_c {
            addr inside {[64:127]};
        }
        
        // Constraint 2: Data patterns
        constraint data_small_c {
            data < 32'h100;
        }
        
        constraint data_large_c {
            data > 32'hFFFF_FF00;
        }
        
        // Constraint 3: Priority
        constraint priority_c {
            priority != 2'b11;
        }
        
        function new();
            // Start with all constraints enabled
        endfunction
        
        function void set_low_addr_mode();
            addr_low_c.constraint_mode(1);   // Enable
            addr_high_c.constraint_mode(0);  // Disable
        endfunction
        
        function void set_high_addr_mode();
            addr_low_c.constraint_mode(0);
            addr_high_c.constraint_mode(1);
        endfunction
        
        function void set_small_data_mode();
            data_small_c.constraint_mode(1);
            data_large_c.constraint_mode(0);
        endfunction
        
        function void set_large_data_mode();
            data_small_c.constraint_mode(0);
            data_large_c.constraint_mode(1);
        endfunction
        
        function void unconstrained_mode();
            // Disable all custom constraints
            addr_low_c.constraint_mode(0);
            addr_high_c.constraint_mode(0);
            data_small_c.constraint_mode(0);
            data_large_c.constraint_mode(0);
        endfunction
    endclass
    
    // Random variable control
    class selective_random;
        rand bit [7:0] field1;
        rand bit [7:0] field2;
        rand bit [7:0] field3;
        
        constraint all_different_c {
            field1 != field2;
            field2 != field3;
            field1 != field3;
        }
        
        function void only_randomize_field1();
            field2.rand_mode(0);  // Make non-random
            field3.rand_mode(0);
        endfunction
        
        function void only_randomize_field2();
            field1.rand_mode(0);
            field3.rand_mode(0);
        endfunction
        
        function void randomize_all();
            field1.rand_mode(1);
            field2.rand_mode(1);
            field3.rand_mode(1);
        endfunction
    endclass
    
    // Configuration-driven constraints
    class config_packet;
        rand bit [7:0] data;
        
        // Multiple constraint sets for different scenarios
        constraint debug_c {
            data inside {[0:15]};
        }
        
        constraint normal_c {
            data inside {[16:239]};
        }
        
        constraint stress_c {
            data inside {[240:255]};
        }
        
        typedef enum {DEBUG_MODE, NORMAL_MODE, STRESS_MODE} mode_e;
        
        function void set_mode(mode_e mode);
            // Disable all
            debug_c.constraint_mode(0);
            normal_c.constraint_mode(0);
            stress_c.constraint_mode(0);
            
            // Enable selected
            case (mode)
                DEBUG_MODE:  debug_c.constraint_mode(1);
                NORMAL_MODE: normal_c.constraint_mode(1);
                STRESS_MODE: stress_c.constraint_mode(1);
            endcase
        endfunction
    endclass
    
    // Runtime constraint switching
    class adaptive_generator;
        rand bit [15:0] value;
        int iteration;
        
        constraint early_c {
            value inside {[0:1000]};
        }
        
        constraint late_c {
            value inside {[60000:65535]};
        }
        
        function void update_constraints();
            if (iteration < 100) begin
                early_c.constraint_mode(1);
                late_c.constraint_mode(0);
            end else begin
                early_c.constraint_mode(0);
                late_c.constraint_mode(1);
            end
        endfunction
        
        function bit do_randomize();
            update_constraints();
            iteration++;
            return randomize();
        endfunction
    endclass
    
    // Hierarchical constraint control
    class packet_with_status;
        rand bit [7:0] data;
        bit constraint_violated;
        
        constraint safe_c {
            data inside {[10:240]};
        }
        
        function bit safe_randomize();
            safe_c.constraint_mode(1);
            if (!randomize()) begin
                constraint_violated = 1;
                return 0;
            end
            return 1;
        endfunction
        
        function bit unsafe_randomize();
            safe_c.constraint_mode(0);
            return randomize();
        endfunction
    endclass
    
    initial begin
        flexible_packet flex;
        selective_random sel;
        config_packet cfg;
        adaptive_generator gen;
        
        $display("=== Dynamic Constraint Control ===\n");
        
        // Flexible packet with modes
        $display("--- Flexible Packet Modes ---");
        flex = new();
        
        flex.set_low_addr_mode();
        flex.set_small_data_mode();
        repeat(3) begin
            assert(flex.randomize());
            $display("Low/Small: addr=%0d, data=0x%0h", flex.addr, flex.data);
        end
        
        flex.set_high_addr_mode();
        flex.set_large_data_mode();
        repeat(3) begin
            assert(flex.randomize());
            $display("High/Large: addr=%0d, data=0x%0h", flex.addr, flex.data);
        end
        
        flex.unconstrained_mode();
        repeat(3) begin
            assert(flex.randomize());
            $display("Unconstrained: addr=%0d, data=0x%0h", flex.addr, flex.data);
        end
        
        // Selective randomization
        $display("\n--- Selective Randomization ---");
        sel = new();
        
        sel.field1 = 8'h11;
        sel.field2 = 8'h22;
        sel.field3 = 8'h33;
        
        sel.only_randomize_field1();
        repeat(3) begin
            assert(sel.randomize());
            $display("Only field1 random: f1=%0h, f2=%0h, f3=%0h", 
                    sel.field1, sel.field2, sel.field3);
        end
        
        // Configuration-driven
        $display("\n--- Configuration Modes ---");
        cfg = new();
        
        cfg.set_mode(config_packet::DEBUG_MODE);
        repeat(2) begin
            assert(cfg.randomize());
            $display("DEBUG: data=%0d", cfg.data);
        end
        
        cfg.set_mode(config_packet::STRESS_MODE);
        repeat(2) begin
            assert(cfg.randomize());
            $display("STRESS: data=%0d", cfg.data);
        end
        
        // Adaptive generation
        $display("\n--- Adaptive Generation ---");
        gen = new();
        gen.iteration = 0;
        
        $display("Early phase (0-99):");
        repeat(3) begin
            assert(gen.do_randomize());
            $display("  iteration %0d: value=%0d", gen.iteration-1, gen.value);
        end
        
        gen.iteration = 100;
        $display("Late phase (100+):");
        repeat(3) begin
            assert(gen.do_randomize());
            $display("  iteration %0d: value=%0d", gen.iteration-1, gen.value);
        end
    end
    
endmodule

/*
 * CONSTRAINT_MODE() AND RAND_MODE():
 * 
 * CONSTRAINT_MODE:
 *   constraint_name.constraint_mode(1);  // Enable
 *   constraint_name.constraint_mode(0);  // Disable
 * 
 * RAND_MODE:
 *   variable.rand_mode(1);  // Make random
 *   variable.rand_mode(0);  // Make non-random (keep current value)
 * 
 * USE CASES:
 * 1. Different test scenarios (debug vs stress)
 * 2. Progressive testing (early vs late phase)
 * 3. Selective randomization (fix some, randomize others)
 * 4. Runtime adaptation based on coverage
 * 5. Error injection control
 * 
 * BEST PRACTICES:
 * - Name constraints descriptively
 * - Document which constraints are mutually exclusive
 * - Provide mode-setting functions
 * - Be careful with constraint interdependencies
 * 
 * PERFORMANCE:
 * - Disabling unused constraints improves solver speed
 * - Fixing variables (rand_mode(0)) reduces solution space
 * - Use for iterative refinement of test scenarios
 */
