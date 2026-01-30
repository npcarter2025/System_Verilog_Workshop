// ============================================================================
// pre_post_randomize.sv - Pre and Post Randomization Functions
// ============================================================================

module pre_post_randomize;
    
    // Basic example with pre_randomize and post_randomize
    class basic_packet;
        rand bit [7:0] data;
        rand bit [7:0] checksum;
        
        int randomize_count;
        
        // Called BEFORE randomization
        function void pre_randomize();
            randomize_count++;
            $display("[PRE] Randomization #%0d starting", randomize_count);
        endfunction
        
        // Called AFTER randomization
        function void post_randomize();
            // Calculate checksum based on randomized data
            checksum = ~data;
            $display("[POST] data=0x%0h, checksum=0x%0h", data, checksum);
        endfunction
    endclass
    
    // Dependent field calculation
    class address_packet;
        rand bit [31:0] base_addr;
        rand bit [15:0] offset;
        bit [31:0] final_addr;  // Not randomized - calculated
        
        constraint addr_c {
            base_addr[1:0] == 2'b00;  // Word aligned
            offset < 16'h1000;
        }
        
        function void post_randomize();
            final_addr = base_addr + offset;
            $display("base=0x%0h + offset=0x%0h = final=0x%0h",
                    base_addr, offset, final_addr);
        endfunction
    endclass
    
    // Statistics tracking
    class tracked_packet;
        rand bit [7:0] value;
        
        static int total_randomizations;
        static int value_sum;
        static real value_avg;
        
        constraint value_c {
            value inside {[10:100]};
        }
        
        function void post_randomize();
            total_randomizations++;
            value_sum += value;
            value_avg = real'(value_sum) / real'(total_randomizations);
            
            if (total_randomizations % 10 == 0) begin
                $display("Stats after %0d randomizations: avg=%0.2f",
                        total_randomizations, value_avg);
            end
        endfunction
    endclass
    
    // Conditional constraint adjustment
    class adaptive_packet;
        rand bit [15:0] data;
        bit high_mode;
        int attempt_count;
        
        constraint data_c {
            if (high_mode)
                data > 16'h8000;
            else
                data < 16'h8000;
        }
        
        function void pre_randomize();
            attempt_count++;
            
            // Switch mode every 5 attempts
            if (attempt_count % 5 == 0) begin
                high_mode = ~high_mode;
                $display("[PRE] Switching to %s mode", 
                        high_mode ? "HIGH" : "LOW");
            end
        endfunction
        
        function void post_randomize();
            $display("  data=0x%0h (%s)", data, high_mode ? "HIGH" : "LOW");
        endfunction
    endclass
    
    // Validation in post_randomize
    class validated_packet;
        rand bit [7:0] header;
        rand bit [31:0] payload;
        rand bit [7:0] footer;
        bit valid;
        
        function void post_randomize();
            // Validation rules
            valid = 1;
            
            // Rule 1: Header must be even
            if (header[0] == 1) begin
                $display("Warning: Invalid header (odd)");
                valid = 0;
            end
            
            // Rule 2: Footer must match header
            if (footer != ~header) begin
                $display("Warning: Footer mismatch");
                valid = 0;
                footer = ~header;  // Auto-correct
            end
            
            // Rule 3: Payload cannot be all zeros
            if (payload == 0) begin
                $display("Warning: Zero payload");
                valid = 0;
                payload = 32'hDEADBEEF;  // Default value
            end
            
            if (valid) begin
                $display("Packet valid: h=0x%0h, p=0x%0h, f=0x%0h",
                        header, payload, footer);
            end
        endfunction
    endclass
    
    // Hierarchical randomization
    class header_obj;
        rand bit [7:0] id;
        rand bit [7:0] seq_num;
        
        static int next_seq_num = 0;
        
        function void post_randomize();
            seq_num = next_seq_num++;
            $display("  [HEADER] id=0x%0h, seq=%0d", id, seq_num);
        endfunction
    endclass
    
    class payload_obj;
        rand bit [31:0] data;
        
        function void post_randomize();
            $display("  [PAYLOAD] data=0x%0h", data);
        endfunction
    endclass
    
    class composite_packet;
        rand header_obj header;
        rand payload_obj payload;
        
        function new();
            header = new();
            payload = new();
        endfunction
        
        function void pre_randomize();
            $display("[COMPOSITE PRE] Starting randomization");
        endfunction
        
        function void post_randomize();
            $display("[COMPOSITE POST] Complete");
        endfunction
    endclass
    
    // Debug hooks
    class debug_packet;
        rand bit [15:0] value;
        bit debug_mode = 1;
        
        function void pre_randomize();
            if (debug_mode) begin
                $display("[DEBUG PRE] value before = 0x%0h", value);
            end
        endfunction
        
        function void post_randomize();
            if (debug_mode) begin
                $display("[DEBUG POST] value after = 0x%0h", value);
                
                // Debug information
                $display("  Binary: %016b", value);
                $display("  Bit count: %0d", $countones(value));
            end
        endfunction
    endclass
    
    initial begin
        basic_packet basic;
        address_packet addr;
        tracked_packet tracked;
        adaptive_packet adapt;
        validated_packet valid;
        composite_packet comp;
        debug_packet dbg;
        
        $display("=== Pre/Post Randomize Examples ===\n");
        
        // Basic usage
        $display("--- Basic Pre/Post ---");
        basic = new();
        repeat(3) begin
            assert(basic.randomize());
        end
        
        // Dependent field
        $display("\n--- Dependent Field Calculation ---");
        addr = new();
        repeat(3) begin
            assert(addr.randomize());
        end
        
        // Statistics
        $display("\n--- Statistics Tracking ---");
        tracked = new();
        repeat(25) begin
            assert(tracked.randomize());
        end
        
        // Adaptive mode
        $display("\n--- Adaptive Constraints ---");
        adapt = new();
        repeat(12) begin
            assert(adapt.randomize());
        end
        
        // Validation
        $display("\n--- Post-Randomization Validation ---");
        valid = new();
        repeat(3) begin
            assert(valid.randomize());
        end
        
        // Hierarchical
        $display("\n--- Hierarchical Randomization ---");
        comp = new();
        repeat(3) begin
            assert(comp.randomize());
        end
        
        // Debug
        $display("\n--- Debug Hooks ---");
        dbg = new();
        assert(dbg.randomize());
    end
    
endmodule

/*
 * PRE_RANDOMIZE / POST_RANDOMIZE:
 * 
 * EXECUTION ORDER:
 * 1. pre_randomize() called
 * 2. Constraints solved, random variables set
 * 3. post_randomize() called
 * 
 * PRE_RANDOMIZE USE CASES:
 * - Set up constraints dynamically
 * - Count randomization attempts
 * - Log state before randomization
 * - Initialize non-random fields
 * - Switch between modes
 * 
 * POST_RANDOMIZE USE CASES:
 * - Calculate dependent fields (checksum, parity, etc.)
 * - Validate randomized values
 * - Apply transformations
 * - Update statistics
 * - Debug/logging
 * - Auto-correction of invalid combinations
 * 
 * IMPORTANT NOTES:
 * 1. post_randomize() CAN modify rand variables
 * 2. Changes in post_randomize() won't affect constraints
 * 3. Hierarchical: parent's post_randomize() after children's
 * 4. Must be virtual functions (not tasks)
 * 5. Called automatically by randomize()
 * 
 * BEST PRACTICES:
 * - Keep them lightweight
 * - Don't put complex logic
 * - Use for final fixups, not primary constraints
 * - Document side effects
 * - Avoid circular dependencies
 * 
 * ANTI-PATTERNS:
 * ❌ Don't put constraints in post_randomize()
 * ❌ Don't do expensive calculations
 * ❌ Don't fail randomization silently
 * ❌ Don't modify state in pre_randomize()
 * ✅ DO use for dependent field calculation
 * ✅ DO use for validation and logging
 */
