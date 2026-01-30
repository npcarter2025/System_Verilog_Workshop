// ============================================================================
// config_patterns.sv - Advanced Configuration Patterns
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// ============================================================================
// PATTERN 1: Layered Configuration (Inheritance)
// ============================================================================

class base_config extends uvm_object;
    int base_timeout = 1000;
    bit enable_logging = 1;
    
    `uvm_object_utils_begin(base_config)
        `uvm_field_int(base_timeout, UVM_ALL_ON)
        `uvm_field_int(enable_logging, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "base_config");
        super.new(name);
    endfunction
endclass

class extended_config extends base_config;
    bit [31:0] start_addr;
    bit [31:0] end_addr;
    int num_transactions = 100;
    
    `uvm_object_utils_begin(extended_config)
        `uvm_field_int(start_addr, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(end_addr, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(num_transactions, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "extended_config");
        super.new(name);
        start_addr = 32'h0000;
        end_addr = 32'hFFFF;
    endfunction
endclass

// ============================================================================
// PATTERN 2: Configuration Object with Constraints
// ============================================================================

class constrained_config extends uvm_object;
    rand int num_agents;
    rand int buffer_depth;
    rand int timeout;
    
    constraint reasonable_c {
        num_agents inside {[1:4]};
        buffer_depth inside {[4, 8, 16, 32]};
        timeout inside {[100:10000]};
        
        // Dependent constraints
        (num_agents > 2) -> (buffer_depth >= 16);
    }
    
    `uvm_object_utils_begin(constrained_config)
        `uvm_field_int(num_agents, UVM_ALL_ON)
        `uvm_field_int(buffer_depth, UVM_ALL_ON)
        `uvm_field_int(timeout, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "constrained_config");
        super.new(name);
    endfunction
    
    // Override constraints for specific scenarios
    function void set_low_resource_mode();
        num_agents = 1;
        buffer_depth = 4;
        timeout = 100;
    endfunction
    
    function void set_stress_mode();
        num_agents = 4;
        buffer_depth = 32;
        timeout = 10000;
    endfunction
endclass

// ============================================================================
// PATTERN 3: Configuration Factory
// ============================================================================

class config_factory extends uvm_object;
    `uvm_object_utils(config_factory)
    
    typedef enum {
        SMOKE_TEST,
        REGRESSION_TEST,
        STRESS_TEST,
        DEBUG_TEST
    } test_mode_e;
    
    function new(string name = "config_factory");
        super.new(name);
    endfunction
    
    static function extended_config create_config(test_mode_e mode);
        extended_config cfg = extended_config::type_id::create("cfg");
        
        case (mode)
            SMOKE_TEST: begin
                cfg.num_transactions = 10;
                cfg.base_timeout = 100;
                cfg.enable_logging = 0;
            end
            
            REGRESSION_TEST: begin
                cfg.num_transactions = 1000;
                cfg.base_timeout = 1000;
                cfg.enable_logging = 0;
            end
            
            STRESS_TEST: begin
                cfg.num_transactions = 10000;
                cfg.base_timeout = 10000;
                cfg.enable_logging = 1;
            end
            
            DEBUG_TEST: begin
                cfg.num_transactions = 5;
                cfg.base_timeout = 100000;
                cfg.enable_logging = 1;
            end
        endcase
        
        return cfg;
    endfunction
endclass

// ============================================================================
// PATTERN 4: Dynamic Runtime Configuration
// ============================================================================

class runtime_config extends uvm_object;
    int current_mode;
    real current_bandwidth;
    bit throttle_enable;
    
    `uvm_object_utils_begin(runtime_config)
        `uvm_field_int(current_mode, UVM_ALL_ON)
        `uvm_field_real(current_bandwidth, UVM_ALL_ON)
        `uvm_field_int(throttle_enable, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "runtime_config");
        super.new(name);
        current_mode = 0;
        current_bandwidth = 1.0;
        throttle_enable = 0;
    endfunction
    
    function void update_from_monitor(int new_mode, real new_bw);
        if (new_mode != current_mode) begin
            `uvm_info("RUNTIME_CONFIG", 
                     $sformatf("Mode change: %0d -> %0d", current_mode, new_mode),
                     UVM_MEDIUM)
            current_mode = new_mode;
        end
        
        if (new_bw < 0.5 && !throttle_enable) begin
            throttle_enable = 1;
            `uvm_warning("RUNTIME_CONFIG", "Low bandwidth - enabling throttle")
        end
        
        current_bandwidth = new_bw;
    endfunction
endclass

// ============================================================================
// PATTERN 5: Configuration with Callbacks
// ============================================================================

class config_callback extends uvm_callback;
    `uvm_object_utils(config_callback)
    
    function new(string name = "config_callback");
        super.new(name);
    endfunction
    
    virtual function void pre_randomize(constrained_config cfg);
    endfunction
    
    virtual function void post_randomize(constrained_config cfg);
    endfunction
endclass

class config_validator_cb extends config_callback;
    `uvm_object_utils(config_validator_cb)
    
    function new(string name = "config_validator_cb");
        super.new(name);
    endfunction
    
    function void post_randomize(constrained_config cfg);
        if (cfg.buffer_depth < cfg.num_agents * 4) begin
            `uvm_warning("CONFIG_VALIDATOR", 
                        $sformatf("Buffer may be too small: %0d for %0d agents",
                                 cfg.buffer_depth, cfg.num_agents))
        end
    endfunction
endclass

// ============================================================================
// TEST: Demonstrating All Patterns
// ============================================================================

class component_using_configs extends uvm_component;
    `uvm_component_utils(component_using_configs)
    
    extended_config cfg;
    runtime_config rt_cfg;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        if (!uvm_config_db#(extended_config)::get(this, "", "cfg", cfg)) begin
            `uvm_warning(get_type_name(), "No config found, using defaults")
            cfg = extended_config::type_id::create("cfg");
        end else begin
            `uvm_info(get_type_name(), "Configuration retrieved:", UVM_LOW)
            cfg.print();
        end
        
        // Get runtime config
        if (!uvm_config_db#(runtime_config)::get(this, "", "rt_cfg", rt_cfg)) begin
            rt_cfg = runtime_config::type_id::create("rt_cfg");
        end
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        repeat(cfg.num_transactions) begin
            // Simulate work based on config
            #(cfg.base_timeout * 0.1 * 1ns);
            
            if (cfg.enable_logging) begin
                `uvm_info(get_type_name(), "Processing transaction", UVM_HIGH)
            end
        end
        
        phase.drop_objection(this);
    endtask
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    
    component_using_configs comp;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        extended_config cfg;
        constrained_config const_cfg;
        runtime_config rt_cfg;
        config_validator_cb validator;
        
        `uvm_info(get_type_name(), "=== Advanced Configuration Patterns ===", UVM_LOW)
        
        // Pattern 1: Layered configuration
        `uvm_info(get_type_name(), "\nPattern 1: Layered Configuration", UVM_LOW)
        cfg = config_factory::create_config(config_factory::SMOKE_TEST);
        cfg.start_addr = 32'h1000;
        cfg.end_addr = 32'h2000;
        
        // Pattern 2: Constrained configuration
        `uvm_info(get_type_name(), "\nPattern 2: Constrained Configuration", UVM_LOW)
        const_cfg = constrained_config::type_id::create("const_cfg");
        assert(const_cfg.randomize());
        const_cfg.print();
        
        // Pattern 3: Configuration factory (already used above)
        `uvm_info(get_type_name(), "\nPattern 3: Configuration Factory", UVM_LOW)
        
        // Pattern 4: Runtime configuration
        `uvm_info(get_type_name(), "\nPattern 4: Runtime Configuration", UVM_LOW)
        rt_cfg = runtime_config::type_id::create("rt_cfg");
        rt_cfg.update_from_monitor(1, 0.8);
        
        // Pattern 5: Configuration callbacks
        `uvm_info(get_type_name(), "\nPattern 5: Configuration Callbacks", UVM_LOW)
        validator = config_validator_cb::type_id::create("validator");
        validator.post_randomize(const_cfg);
        
        // Set configurations
        uvm_config_db#(extended_config)::set(this, "comp", "cfg", cfg);
        uvm_config_db#(runtime_config)::set(this, "comp", "rt_cfg", rt_cfg);
        
        comp = component_using_configs::type_id::create("comp", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        #1us;
        phase.drop_objection(this);
    endtask
    
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "All configuration patterns demonstrated", UVM_LOW)
    endfunction
endclass

module top;
    initial run_test("test");
endmodule

/*
 * CONFIGURATION BEST PRACTICES:
 * 
 * 1. LAYERED CONFIG: Use inheritance for common settings
 * 2. CONSTRAINTS: Validate configuration values
 * 3. FACTORY: Centralize config creation for test modes
 * 4. RUNTIME: Allow dynamic updates during simulation
 * 5. CALLBACKS: Add validation and transformation hooks
 * 
 * ANTI-PATTERNS TO AVOID:
 * - Hardcoded values in components
 * - Passing configs through constructors
 * - Modifying shared config objects
 * - Missing validation of config values
 * - No defaults for optional settings
 */
