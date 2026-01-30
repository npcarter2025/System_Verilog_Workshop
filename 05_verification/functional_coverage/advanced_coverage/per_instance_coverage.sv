// ============================================================================
// per_instance_coverage.sv - Per-Instance vs Type Coverage
// ============================================================================

module per_instance_coverage;
    
    // ========================================================================
    // Type Coverage (Default - Merged Across Instances)
    // ========================================================================
    
    class transaction_type_coverage;
        rand bit [3:0] value;
        int instance_id;
        
        covergroup cg;
            option.per_instance = 0;  // Default: merge all instances
            
            cp_value: coverpoint value {
                bins low = {[0:7]};
                bins high = {[8:15]};
            }
        endgroup
        
        function new(int id);
            instance_id = id;
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Per-Instance Coverage (Separate for Each Instance)
    // ========================================================================
    
    class transaction_per_instance;
        rand bit [3:0] value;
        int instance_id;
        
        covergroup cg;
            option.per_instance = 1;  // Separate coverage per instance
            option.name = "per_instance_cg";
            
            cp_value: coverpoint value {
                bins low = {[0:7]};
                bins high = {[8:15]};
            }
        endgroup
        
        function new(int id);
            instance_id = id;
            cg = new();
        endfunction
    endclass
    
    // ========================================================================
    // Use Case: Multiple Agents
    // ========================================================================
    
    typedef enum bit [1:0] {READ, WRITE, IDLE, ERROR} op_e;
    
    class agent_transaction;
        rand op_e operation;
        rand bit [7:0] addr;
        string agent_name;
        
        covergroup cg;
            option.per_instance = 1;  // Track each agent separately
            
            cp_op: coverpoint operation {
                bins read_op = {READ};
                bins write_op = {WRITE};
                bins idle_op = {IDLE};
                bins error_op = {ERROR};
            }
            
            cp_addr: coverpoint addr {
                bins low_addr = {[0:63]};
                bins mid_addr = {[64:191]};
                bins high_addr = {[192:255]};
            }
        endgroup
        
        function new(string name);
            agent_name = name;
            cg = new();
        endfunction
        
        function void print_coverage();
            $display("%s coverage: %0.2f%%", agent_name, cg.get_coverage());
        endfunction
    endclass
    
    // ========================================================================
    // Use Case: Multiple Interfaces
    // ========================================================================
    
    class interface_monitor;
        rand bit [1:0] state;
        rand bit error;
        string interface_name;
        int port_num;
        
        covergroup cg;
            option.per_instance = 1;
            option.name = "interface_cg";
            
            cp_state: coverpoint state {
                bins idle = {0};
                bins active = {1};
                bins wait_st = {2};
                bins done = {3};
            }
            
            cp_error: coverpoint error {
                bins no_error = {0};
                bins has_error = {1};
            }
            
            cross_state_error: cross cp_state, cp_error;
        endgroup
        
        function new(string name, int port);
            interface_name = name;
            port_num = port;
            cg = new();
        endfunction
        
        function void print_coverage();
            $display("Interface %s[%0d]: %0.2f%%", 
                    interface_name, port_num, cg.get_coverage());
        endfunction
    endclass
    
    // ========================================================================
    // Comparison: Type vs Per-Instance
    // ========================================================================
    
    class comparison_example;
        rand bit [2:0] value;
        int id;
        
        covergroup cg_type;
            option.per_instance = 0;  // Type coverage
            cp_value: coverpoint value;
        endgroup
        
        covergroup cg_instance;
            option.per_instance = 1;  // Per-instance coverage
            cp_value: coverpoint value;
        endgroup
        
        function new(int instance_id);
            id = instance_id;
            cg_type = new();
            cg_instance = new();
        endfunction
        
        function void sample();
            cg_type.sample();
            cg_instance.sample();
        endfunction
        
        function void print_coverage();
            $display("Instance %0d:", id);
            $display("  Type coverage: %0.2f%%", cg_type.get_coverage());
            $display("  Per-instance coverage: %0.2f%%", cg_instance.get_coverage());
        endfunction
    endclass
    
    // ========================================================================
    // Per-Instance with Name
    // ========================================================================
    
    class named_instance;
        rand bit [3:0] value;
        string name;
        
        covergroup cg (string inst_name);
            option.per_instance = 1;
            option.name = inst_name;
            
            cp_value: coverpoint value {
                bins low = {[0:7]};
                bins high = {[8:15]};
            }
        endgroup
        
        function new(string n);
            name = n;
            cg = new(name);
        endfunction
        
        function void print_coverage();
            $display("%s: %0.2f%%", name, cg.get_coverage());
        endfunction
    endclass
    
    // ========================================================================
    // Use Case: Master-Slave Configuration
    // ========================================================================
    
    typedef enum {MASTER, SLAVE} role_e;
    
    class bus_agent;
        rand bit [7:0] data;
        rand bit [15:0] addr;
        role_e role;
        int agent_id;
        
        covergroup cg;
            option.per_instance = 1;
            
            cp_data: coverpoint data {
                bins zeros = {0};
                bins ones = {8'hFF};
                bins others = {[1:254]};
            }
            
            cp_addr: coverpoint addr {
                bins low = {[0:16'h3FFF]};
                bins high = {[16'h4000:16'hFFFF]};
            }
            
            cross_data_addr: cross cp_data, cp_addr;
        endgroup
        
        function new(role_e r, int id);
            role = r;
            agent_id = id;
            cg = new();
        endfunction
        
        function void sample();
            cg.sample();
        endfunction
        
        function void print_coverage();
            $display("%s[%0d]: %0.2f%%", 
                    role.name(), agent_id, cg.get_coverage());
        endfunction
    endclass
    
    // ========================================================================
    // Dynamic Instances
    // ========================================================================
    
    class dynamic_instance;
        rand bit [2:0] cmd;
        int instance_num;
        static int num_instances = 0;
        
        covergroup cg;
            option.per_instance = 1;
            
            cp_cmd: coverpoint cmd {
                bins cmds[] = {[0:7]};
            }
        endgroup
        
        function new();
            instance_num = num_instances++;
            cg = new();
            $display("Created instance %0d", instance_num);
        endfunction
        
        function void sample();
            cg.sample();
        endfunction
        
        function real get_coverage();
            return cg.get_coverage();
        endfunction
    endclass
    
    // ========================================================================
    // Per-Instance with Hierarch
ical Access
    // ========================================================================
    
    class port_monitor;
        rand bit [3:0] status;
        int port_id;
        string path;
        
        covergroup cg;
            option.per_instance = 1;
            
            cp_status: coverpoint status {
                bins idle = {0};
                bins active = {[1:7]};
                bins busy = {8};
                bins error = {[9:15]};
            }
        endgroup
        
        function new(int id, string hier_path);
            port_id = id;
            path = hier_path;
            cg = new();
        endfunction
        
        function void sample();
            cg.sample();
        endfunction
        
        function void print_status();
            $display("Port %0d (%s): %0.2f%% coverage", 
                    port_id, path, cg.get_coverage());
        endfunction
    endclass
    
    // ========================================================================
    // Real-World: Multi-Channel DMA
    // ========================================================================
    
    typedef enum bit [1:0] {IDLE_DMA, TRANSFER, WAIT_DMA, DONE_DMA} dma_state_e;
    
    class dma_channel;
        rand dma_state_e state;
        rand bit [31:0] src_addr;
        rand bit [31:0] dst_addr;
        rand bit [15:0] transfer_size;
        rand bit error;
        
        int channel_id;
        string channel_name;
        
        covergroup cg;
            option.per_instance = 1;
            option.comment = "DMA Channel Coverage";
            
            cp_state: coverpoint state {
                bins idle = {IDLE_DMA};
                bins transfer = {TRANSFER};
                bins wait_st = {WAIT_DMA};
                bins done = {DONE_DMA};
                
                // State transitions
                bins start_xfer = (IDLE_DMA => TRANSFER);
                bins complete = (TRANSFER => DONE_DMA);
                bins pause = (TRANSFER => WAIT_DMA => TRANSFER);
                bins restart = (DONE_DMA => IDLE_DMA);
            }
            
            cp_size: coverpoint transfer_size {
                bins small = {[1:255]};
                bins medium = {[256:4095]};
                bins large = {[4096:65535]};
            }
            
            cp_src_align: coverpoint src_addr[1:0] {
                bins aligned = {2'b00};
                bins unaligned = {2'b01, 2'b10, 2'b11};
            }
            
            cp_dst_align: coverpoint dst_addr[1:0] {
                bins aligned = {2'b00};
                bins unaligned = {2'b01, 2'b10, 2'b11};
            }
            
            cp_error: coverpoint error;
            
            // Important cross coverage
            cross_align: cross cp_src_align, cp_dst_align {
                option.weight = 5;
            }
            
            cross_size_error: cross cp_size, cp_error;
        endgroup
        
        function new(int id, string name);
            channel_id = id;
            channel_name = name;
            cg = new();
            state = IDLE_DMA;
        endfunction
        
        function void sample();
            cg.sample();
        endfunction
        
        function void print_summary();
            $display("\n=== DMA Channel %s [%0d] ===", channel_name, channel_id);
            $display("State coverage:       %0.2f%%", cg.cp_state.get_coverage());
            $display("Size coverage:        %0.2f%%", cg.cp_size.get_coverage());
            $display("Src align coverage:   %0.2f%%", cg.cp_src_align.get_coverage());
            $display("Dst align coverage:   %0.2f%%", cg.cp_dst_align.get_coverage());
            $display("Alignment cross:      %0.2f%%", cg.cross_align.get_coverage());
            $display("Overall coverage:     %0.2f%%", cg.get_coverage());
        endfunction
    endclass
    
    initial begin
        transaction_type_coverage type_cov[];
        transaction_per_instance inst_cov[];
        agent_transaction agents[];
        interface_monitor interfaces[];
        comparison_example comp[];
        bus_agent masters[];
        bus_agent slaves[];
        dma_channel dma_channels[];
        
        $display("=== Per-Instance Coverage Examples ===\n");
        
        // Type coverage (merged)
        $display("--- Type Coverage (Merged) ---");
        type_cov = new[3];
        foreach(type_cov[i]) begin
            type_cov[i] = new(i);
            repeat(20) begin
                assert(type_cov[i].randomize());
                type_cov[i].cg.sample();
            end
        end
        $display("Merged coverage: %0.2f%%", type_cov[0].cg.get_coverage());
        
        // Per-instance coverage
        $display("\n--- Per-Instance Coverage (Separate) ---");
        inst_cov = new[3];
        foreach(inst_cov[i]) begin
            inst_cov[i] = new(i);
            repeat(10 + i*5) begin  // Different amounts per instance
                assert(inst_cov[i].randomize());
                inst_cov[i].cg.sample();
            end
            $display("Instance %0d coverage: %0.2f%%", i, inst_cov[i].cg.get_coverage());
        end
        
        // Multiple agents
        $display("\n--- Multiple Agents ---");
        agents = new[4];
        agents[0] = new("Master_0");
        agents[1] = new("Master_1");
        agents[2] = new("Slave_0");
        agents[3] = new("Slave_1");
        
        foreach(agents[i]) begin
            repeat(50) begin
                assert(agents[i].randomize());
                agents[i].cg.sample();
            end
            agents[i].print_coverage();
        end
        
        // Multiple interfaces
        $display("\n--- Multiple Interface Ports ---");
        interfaces = new[4];
        foreach(interfaces[i]) begin
            interfaces[i] = new($sformatf("AXI"), i);
            repeat(30) begin
                assert(interfaces[i].randomize());
                interfaces[i].cg.sample();
            end
            interfaces[i].print_coverage();
        end
        
        // Comparison
        $display("\n--- Type vs Per-Instance Comparison ---");
        comp = new[2];
        foreach(comp[i]) begin
            comp[i] = new(i);
            // Instance 0: only low values
            // Instance 1: only high values
            repeat(20) begin
                assert(comp[i].randomize() with {
                    value inside {[i*4:(i+1)*4-1]};
                });
                comp[i].sample();
            end
        end
        foreach(comp[i]) comp[i].print_coverage();
        $display("Notice: Type coverage merges, per-instance is separate");
        
        // Master-slave
        $display("\n--- Master-Slave Configuration ---");
        masters = new[2];
        slaves = new[2];
        foreach(masters[i]) begin
            masters[i] = new(MASTER, i);
            slaves[i] = new(SLAVE, i);
        end
        
        repeat(100) begin
            foreach(masters[i]) begin
                assert(masters[i].randomize());
                masters[i].sample();
            end
            foreach(slaves[i]) begin
                assert(slaves[i].randomize());
                slaves[i].sample();
            end
        end
        
        foreach(masters[i]) masters[i].print_coverage();
        foreach(slaves[i]) slaves[i].print_coverage();
        
        // DMA channels
        $display("\n--- Multi-Channel DMA Example ---");
        dma_channels = new[4];
        dma_channels[0] = new(0, "CH0_MEM2MEM");
        dma_channels[1] = new(1, "CH1_MEM2DEV");
        dma_channels[2] = new(2, "CH2_DEV2MEM");
        dma_channels[3] = new(3, "CH3_DEV2DEV");
        
        repeat(200) begin
            foreach(dma_channels[i]) begin
                assert(dma_channels[i].randomize());
                dma_channels[i].sample();
            end
        end
        
        foreach(dma_channels[i]) begin
            dma_channels[i].print_summary();
        end
    end
    
endmodule

/*
 * PER-INSTANCE COVERAGE:
 * 
 * SYNTAX:
 *   covergroup cg;
 *     option.per_instance = 1;  // Separate tracking per instance
 *   endgroup
 * 
 * TYPE COVERAGE (Default):
 *   option.per_instance = 0;
 *   - All instances of same class share coverage
 *   - Coverage merged across all instances
 *   - One coverage report for the type
 * 
 * PER-INSTANCE COVERAGE:
 *   option.per_instance = 1;
 *   - Each instance has separate coverage
 *   - Independent tracking
 *   - Multiple coverage reports
 * 
 * WHEN TO USE TYPE COVERAGE:
 * - Don't care which instance hits coverage
 * - Want combined/merged coverage
 * - All instances are functionally identical
 * - Saves memory (one copy of bins)
 * - Example: Generic transactions
 * 
 * WHEN TO USE PER-INSTANCE:
 * - Track coverage separately per component
 * - Instances have different roles/behavior
 * - Need to see coverage per agent/port/channel
 * - Debugging: which instance is lacking coverage?
 * - Examples:
 *   * Multiple agents (master vs slave)
 *   * Multiple interfaces/ports
 *   * Multiple channels
 *   * Multiple protocol instances
 * 
 * USE CASES:
 * 1. Multi-port designs (track each port)
 * 2. Multi-agent testbenches (master/slave)
 * 3. Multi-channel systems (DMA, etc.)
 * 4. Redundant systems (compare coverage)
 * 5. Hierarchical verification (sub-blocks)
 * 
 * BENEFITS:
 * - Identify which instances need more testing
 * - Verify all instances exercised equally
 * - Debug coverage holes per component
 * - Better visibility into system behavior
 * 
 * TRADE-OFFS:
 * + Pros:
 *   - Detailed per-component visibility
 *   - Can identify under-tested instances
 *   - Better for multi-instance designs
 * - Cons:
 *   - More memory (separate bins per instance)
 *   - More coverage data to analyze
 *   - Longer merge/reporting time
 * 
 * NAMING:
 * - Use option.name for readable instance names
 * - Include instance ID or role in name
 * - Examples:
 *   * "master_0_cg"
 *   * "axi_port_2"
 *   * "dma_ch3"
 * 
 * COVERAGE QUERIES:
 * - get_coverage(): Returns this instance's coverage
 * - get_inst_coverage(): Same for per-instance
 * - Each instance independently tracked
 * 
 * BEST PRACTICES:
 * 1. Use per-instance for distinct components
 * 2. Use type coverage for interchangeable objects
 * 3. Name instances clearly
 * 4. Compare coverage across instances
 * 5. Investigate unbalanced coverage
 * 6. Document why per-instance is used
 * 
 * EXAMPLE SCENARIOS:
 * - 4-port switch: per-instance for each port
 * - Multi-master bus: per-instance for each master
 * - DMA with channels: per-instance per channel
 * - Redundant paths: per-instance to verify both used
 */
