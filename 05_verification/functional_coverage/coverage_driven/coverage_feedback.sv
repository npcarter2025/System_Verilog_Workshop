// ============================================================================
// coverage_feedback.sv - Coverage-Driven Verification with Feedback
// ============================================================================

module coverage_feedback;
    
    // ========================================================================
    // Basic Coverage-Driven Generation
    // ========================================================================
    
    class basic_coverage_driven;
        rand bit [3:0] value;
        bit [3:0] uncovered_values[$];
        
        covergroup cg;
            cp_value: coverpoint value {
                bins values[] = {[0:15]};
            }
        endgroup
        
        function new();
            cg = new();
            // Initialize with all values
            for (int i = 0; i < 16; i++) begin
                uncovered_values.push_back(i);
            end
        endfunction
        
        function void update_uncovered();
            // Check which bins are not yet covered
            uncovered_values.delete();
            for (int i = 0; i < 16; i++) begin
                // Simplified: real implementation would query bin coverage
                if ($urandom_range(0, 100) < 50)  // Simulating uncovered
                    uncovered_values.push_back(i);
            end
        endfunction
        
        function bit generate_uncovered();
            if (uncovered_values.size() == 0) begin
                update_uncovered();
                if (uncovered_values.size() == 0)
                    return 0;  // All covered
            end
            
            // Pick random uncovered value
            value = uncovered_values[$urandom_range(0, uncovered_values.size()-1)];
            return 1;
        endfunction
    endclass
    
    // ========================================================================
    // Coverage-Driven State Machine
    // ========================================================================
    
    typedef enum bit [1:0] {IDLE, ACTIVE, WAIT, DONE} state_e;
    
    class state_coverage_driven;
        state_e current_state;
        state_e next_state;
        bit [7:0] transition_hits[state_e][state_e];
        int min_hits_per_transition = 3;
        
        covergroup cg;
            cp_state: coverpoint current_state;
            
            cp_transitions: coverpoint current_state {
                bins idle_to_active = (IDLE => ACTIVE);
                bins active_to_wait = (ACTIVE => WAIT);
                bins wait_to_active = (WAIT => ACTIVE);
                bins active_to_done = (ACTIVE => DONE);
                bins done_to_idle = (DONE => IDLE);
            }
        endgroup
        
        function new();
            cg = new();
            current_state = IDLE;
            
            // Initialize hit counters
            foreach(transition_hits[i, j]) begin
                transition_hits[i][j] = 0;
            end
        endfunction
        
        function state_e choose_next_state();
            state_e candidates[$];
            state_e chosen;
            
            // Find transitions that need more coverage
            case (current_state)
                IDLE: begin
                    if (transition_hits[IDLE][ACTIVE] < min_hits_per_transition)
                        candidates.push_back(ACTIVE);
                end
                ACTIVE: begin
                    if (transition_hits[ACTIVE][WAIT] < min_hits_per_transition)
                        candidates.push_back(WAIT);
                    if (transition_hits[ACTIVE][DONE] < min_hits_per_transition)
                        candidates.push_back(DONE);
                end
                WAIT: begin
                    if (transition_hits[WAIT][ACTIVE] < min_hits_per_transition)
                        candidates.push_back(ACTIVE);
                end
                DONE: begin
                    if (transition_hits[DONE][IDLE] < min_hits_per_transition)
                        candidates.push_back(IDLE);
                end
            endcase
            
            // Choose randomly from candidates, or any valid transition
            if (candidates.size() > 0) begin
                chosen = candidates[$urandom_range(0, candidates.size()-1)];
            end else begin
                // All covered, choose any valid transition
                case (current_state)
                    IDLE:   chosen = ACTIVE;
                    ACTIVE: chosen = ($ urandom_range(0, 1)) ? WAIT : DONE;
                    WAIT:   chosen = ACTIVE;
                    DONE:   chosen = IDLE;
                endcase
            end
            
            return chosen;
        endfunction
        
        function void transition();
            next_state = choose_next_state();
            transition_hits[current_state][next_state]++;
            current_state = next_state;
            cg.sample();
        endfunction
        
        function void print_coverage();
            $display("\nTransition Coverage:");
            foreach(transition_hits[i, j]) begin
                if (transition_hits[i][j] > 0) begin
                    $display("  %s -> %s: %0d hits %s", 
                            i.name(), j.name(), transition_hits[i][j],
                            (transition_hits[i][j] >= min_hits_per_transition) ? "(✓)" : "(needs more)");
                end
            end
        endfunction
    endclass
    
    // ========================================================================
    // Adaptive Constraint-Based Generation
    // ========================================================================
    
    class adaptive_generator;
        rand bit [7:0] value;
        real low_range_coverage;
        real mid_range_coverage;
        real high_range_coverage;
        
        covergroup cg;
            cp_value: coverpoint value {
                bins low = {[0:63]};
                bins mid = {[64:191]};
                bins high = {[192:255]};
            }
        endgroup
        
        constraint adaptive_c {
            // Bias toward ranges with lower coverage
            value dist {
                [0:63] := int'((1.0 - low_range_coverage) * 100),
                [64:191] := int'((1.0 - mid_range_coverage) * 100),
                [192:255] := int'((1.0 - high_range_coverage) * 100)
            };
        }
        
        function new();
            cg = new();
            low_range_coverage = 0.0;
            mid_range_coverage = 0.0;
            high_range_coverage = 0.0;
        endfunction
        
        function void update_coverage();
            // In real implementation, query actual bin coverage
            // Here we simulate it
            low_range_coverage = cg.get_coverage() / 300.0;
            mid_range_coverage = cg.get_coverage() / 300.0;
            high_range_coverage = cg.get_coverage() / 300.0;
            
            // Clamp to [0.0, 1.0]
            if (low_range_coverage > 1.0) low_range_coverage = 1.0;
            if (mid_range_coverage > 1.0) mid_range_coverage = 1.0;
            if (high_range_coverage > 1.0) high_range_coverage = 1.0;
        endfunction
        
        function bit generate_next();
            update_coverage();
            
            if (cg.get_coverage() >= 100.0)
                return 0;  // Done
            
            assert(randomize());
            cg.sample();
            return 1;
        endfunction
    endclass
    
    // ========================================================================
    // Coverage Holes Detection and Filling
    // ========================================================================
    
    class hole_filler;
        rand bit [3:0] a;
        rand bit [3:0] b;
        bit [3:0] uncovered_a_values[$];
        bit [3:0] uncovered_b_values[$];
        int generation_mode;  // 0=random, 1=fill_holes
        
        covergroup cg;
            cp_a: coverpoint a {
                bins a_vals[] = {[0:15]};
            }
            
            cp_b: coverpoint b {
                bins b_vals[] = {[0:15]};
            }
            
            cross_ab: cross cp_a, cp_b;
        endgroup
        
        constraint mode_0_c {
            generation_mode == 0;
            // Normal random
        }
        
        constraint mode_1_c {
            generation_mode == 1;
            // Directed toward holes
            if (uncovered_a_values.size() > 0) {
                a inside {uncovered_a_values};
            }
            if (uncovered_b_values.size() > 0) {
                b inside {uncovered_b_values};
            }
        }
        
        function new();
            cg = new();
            generation_mode = 0;
        endfunction
        
        function void find_holes();
            // Simplified: in real implementation, query actual coverage
            uncovered_a_values.delete();
            uncovered_b_values.delete();
            
            // Simulate finding some uncovered values
            if (cg.get_coverage() < 80.0) begin
                for (int i = 0; i < 5; i++) begin
                    uncovered_a_values.push_back($urandom_range(0, 15));
                    uncovered_b_values.push_back($urandom_range(0, 15));
                end
            end
        endfunction
        
        function void fill_holes(int num_transactions);
            generation_mode = 1;
            find_holes();
            
            $display("Filling %0d coverage holes...", 
                    uncovered_a_values.size() + uncovered_b_values.size());
            
            repeat(num_transactions) begin
                assert(randomize());
                cg.sample();
            end
            
            generation_mode = 0;
        endfunction
    endclass
    
    // ========================================================================
    // Coverage-Driven Test Termination
    // ========================================================================
    
    class coverage_termination;
        rand bit [2:0] cmd;
        rand bit [7:0] data;
        real coverage_goal = 95.0;
        int max_iterations = 1000;
        int stall_count = 0;
        int max_stall = 50;  // Stop if no progress for 50 iterations
        real prev_coverage = 0.0;
        
        covergroup cg;
            option.goal = 95;
            
            cp_cmd: coverpoint cmd {
                bins cmds[] = {[0:7]};
            }
            
            cp_data: coverpoint data {
                bins low = {[0:63]};
                bins mid = {[64:191]};
                bins high = {[192:255]};
            }
            
            cross_cmd_data: cross cp_cmd, cp_data;
        endgroup
        
        function new();
            cg = new();
        endfunction
        
        function bit should_continue(int iteration);
            real current_coverage = cg.get_coverage();
            
            // Check if goal reached
            if (current_coverage >= coverage_goal) begin
                $display("Coverage goal %0.1f%% reached at iteration %0d", 
                        coverage_goal, iteration);
                return 0;
            end
            
            // Check max iterations
            if (iteration >= max_iterations) begin
                $display("Max iterations %0d reached, coverage: %0.2f%%", 
                        max_iterations, current_coverage);
                return 0;
            end
            
            // Check for stall (no progress)
            if (current_coverage == prev_coverage) begin
                stall_count++;
                if (stall_count >= max_stall) begin
                    $display("Coverage stalled at %0.2f%% for %0d iterations", 
                            current_coverage, stall_count);
                    return 0;
                end
            end else begin
                stall_count = 0;
            end
            
            prev_coverage = current_coverage;
            return 1;
        endfunction
        
        function void run();
            int iteration = 0;
            
            while (should_continue(iteration)) begin
                assert(randomize());
                cg.sample();
                iteration++;
                
                if (iteration % 100 == 0) begin
                    $display("Iteration %0d: Coverage = %0.2f%%", 
                            iteration, cg.get_coverage());
                end
            end
            
            $display("\nFinal Results:");
            $display("  Total iterations: %0d", iteration);
            $display("  Final coverage: %0.2f%%", cg.get_coverage());
            $display("  Cmd coverage: %0.2f%%", cg.cp_cmd.get_coverage());
            $display("  Data coverage: %0.2f%%", cg.cp_data.get_coverage());
            $display("  Cross coverage: %0.2f%%", cg.cross_cmd_data.get_coverage());
        endfunction
    endclass
    
    // ========================================================================
    // Real-World: AXI Coverage-Driven Generator
    // ========================================================================
    
    typedef enum bit [1:0] {FIXED, INCR, WRAP} burst_e;
    
    class axi_coverage_driven;
        rand bit write;
        rand bit [2:0] size;
        rand bit [7:0] len;
        rand burst_e burst;
        rand bit [31:0] addr;
        
        // Track what needs more coverage
        real write_coverage;
        real read_coverage;
        real size_coverage[4];
        real burst_coverage[3];
        
        covergroup cg;
            option.goal = 95;
            
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
                bins medium_burst = {[8:15]};
                bins long_burst = {[16:255]};
            }
            
            cp_burst: coverpoint burst {
                bins fixed = {FIXED};
                bins incr = {INCR};
                bins wrap = {WRAP};
            }
            
            cross_write_size: cross cp_write, cp_size;
            cross_burst_len: cross cp_burst, cp_len;
        endgroup
        
        constraint valid_c {
            // Basic AXI rules
            (burst == WRAP) -> (len inside {1, 3, 7, 15});
            (size == 1) -> (addr[0] == 0);
            (size == 2) -> (addr[1:0] == 2'b00);
            (size == 3) -> (addr[2:0] == 3'b000);
        }
        
        constraint adaptive_c {
            // Bias toward less-covered options
            write dist {
                0 := int'((1.0 - read_coverage) * 100),
                1 := int'((1.0 - write_coverage) * 100)
            };
        }
        
        function new();
            cg = new();
            write_coverage = 0.0;
            read_coverage = 0.0;
            foreach(size_coverage[i]) size_coverage[i] = 0.0;
            foreach(burst_coverage[i]) burst_coverage[i] = 0.0;
        endfunction
        
        function void update_weights();
            real total_cov = cg.get_coverage();
            
            // Update coverage metrics (simplified)
            write_coverage = total_cov / 200.0;
            read_coverage = total_cov / 200.0;
            
            if (write_coverage > 1.0) write_coverage = 1.0;
            if (read_coverage > 1.0) read_coverage = 1.0;
        endfunction
        
        function bit generate_transaction();
            if (cg.get_coverage() >= cg.option.goal)
                return 0;  // Goal reached
            
            update_weights();
            assert(randomize());
            cg.sample();
            return 1;
        endfunction
        
        function void run_coverage_driven(int max_trans = 1000);
            int count = 0;
            
            $display("Starting coverage-driven generation...");
            $display("Goal: %0.0f%%\n", cg.option.goal);
            
            while (generate_transaction() && count < max_trans) begin
                count++;
                
                if (count % 100 == 0) begin
                    $display("Transaction %0d: Coverage = %0.2f%%", 
                            count, cg.get_coverage());
                end
            end
            
            $display("\n=== Final Coverage Report ===");
            $display("Total transactions: %0d", count);
            $display("Write/Read: %0.2f%%", cg.cp_write.get_coverage());
            $display("Size: %0.2f%%", cg.cp_size.get_coverage());
            $display("Length: %0.2f%%", cg.cp_len.get_coverage());
            $display("Burst: %0.2f%%", cg.cp_burst.get_coverage());
            $display("Write x Size: %0.2f%%", cg.cross_write_size.get_coverage());
            $display("Burst x Length: %0.2f%%", cg.cross_burst_len.get_coverage());
            $display("Overall: %0.2f%%", cg.get_coverage());
        endfunction
    endclass
    
    initial begin
        state_coverage_driven state_gen;
        adaptive_generator adapt;
        hole_filler filler;
        coverage_termination term;
        axi_coverage_driven axi_gen;
        
        $display("=== Coverage-Driven Verification Examples ===\n");
        
        // State machine coverage-driven
        $display("--- Coverage-Driven State Machine ---");
        state_gen = new();
        repeat(50) begin
            state_gen.transition();
        end
        state_gen.print_coverage();
        $display("State coverage: %0.2f%%\n", state_gen.cg.get_coverage());
        
        // Adaptive generation
        $display("--- Adaptive Generator ---");
        adapt = new();
        repeat(200) begin
            if (!adapt.generate_next()) break;
        end
        $display("Final coverage: %0.2f%%\n", adapt.cg.get_coverage());
        
        // Hole filling
        $display("--- Coverage Hole Filling ---");
        filler = new();
        // Random phase
        repeat(100) begin
            assert(filler.randomize());
            filler.cg.sample();
        end
        $display("After random: %0.2f%%", filler.cg.get_coverage());
        // Directed phase
        filler.fill_holes(50);
        $display("After hole filling: %0.2f%%\n", filler.cg.get_coverage());
        
        // Coverage-driven termination
        $display("--- Coverage-Driven Test Termination ---");
        term = new();
        term.run();
        
        // AXI coverage-driven
        $display("\n--- AXI Coverage-Driven Generator ---");
        axi_gen = new();
        axi_gen.run_coverage_driven(2000);
    end
    
endmodule

/*
 * COVERAGE-DRIVEN VERIFICATION (CDV):
 * 
 * CONCEPT:
 * - Use coverage feedback to guide stimulus generation
 * - Focus effort on uncovered areas
 * - Automatically adapt based on coverage progress
 * - Stop when coverage goals met
 * 
 * TECHNIQUES:
 * 1. Query coverage and adjust constraints
 * 2. Bias random generation toward holes
 * 3. Directed generation for specific bins
 * 4. Adaptive weighting based on coverage
 * 5. Two-phase: random then directed
 * 
 * COVERAGE QUERIES:
 * - get_coverage(): Overall percentage
 * - coverpoint.get_coverage(): Specific coverpoint
 * - Can query bin-level coverage (simulator-specific)
 * 
 * BENEFITS:
 * + Faster coverage closure
 * + Efficient test generation
 * + Automatic focus on uncovered areas
 * + Fewer wasted transactions
 * + Intelligent test termination
 * 
 * IMPLEMENTATION PATTERNS:
 * 1. Random + Feedback:
 *    - Generate randomly
 *    - Periodically check coverage
 *    - Adjust constraints based on holes
 * 
 * 2. Two-Phase:
 *    - Phase 1: Pure random (fast, broad)
 *    - Phase 2: Directed at holes (targeted)
 * 
 * 3. Adaptive Constraints:
 *    - Use coverage in dist weights
 *    - Bias toward uncovered values
 *    - Dynamic constraint adjustment
 * 
 * 4. Explicit Hole Filling:
 *    - Query uncovered bins
 *    - Generate transactions for those bins
 *    - Repeat until holes filled
 * 
 * TEST TERMINATION:
 * - Coverage goal reached
 * - Max iterations/time exceeded
 * - Coverage stalled (no progress)
 * - Combination of above
 * 
 * BEST PRACTICES:
 * 1. Set realistic coverage goals (90-95%)
 * 2. Use timeout/iteration limits
 * 3. Detect and handle stalls
 * 4. Balance random vs directed
 * 5. Log coverage progress
 * 6. Identify hard-to-reach bins
 * 7. May need multiple strategies
 * 
 * CHALLENGES:
 * - Some bins may be very hard to hit
 * - Over-constraining can prevent progress
 * - Need to balance efficiency vs thoroughness
 * - Cross coverage explosion
 * - Tool-dependent APIs
 * 
 * COMMON APPLICATIONS:
 * - Protocol verification
 * - State machine testing
 * - Address space coverage
 * - Instruction coverage (processors)
 * - Configuration coverage
 * 
 * METRICS TO TRACK:
 * - Coverage vs time/transactions
 * - Efficiency (coverage gain per transaction)
 * - Coverage holes remaining
 * - Time in each phase
 * - Stall detection
 */
