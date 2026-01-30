// ============================================================================
// config_object.sv - Agent Configuration Object
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// Configuration class
class agent_config extends uvm_object;
    
    // Active/Passive mode
    uvm_active_passive_enum is_active = UVM_ACTIVE;
    
    // Timing parameters
    int unsigned min_delay = 1;
    int unsigned max_delay = 5;
    
    // Coverage enable
    bit coverage_enable = 1;
    
    // Checks enable
    bit checks_enable = 1;
    
    // Address range
    bit [31:0] start_addr = 32'h0000;
    bit [31:0] end_addr = 32'hFFFF;
    
    `uvm_object_utils_begin(agent_config)
        `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_ALL_ON)
        `uvm_field_int(min_delay, UVM_ALL_ON)
        `uvm_field_int(max_delay, UVM_ALL_ON)
        `uvm_field_int(coverage_enable, UVM_ALL_ON)
        `uvm_field_int(checks_enable, UVM_ALL_ON)
        `uvm_field_int(start_addr, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(end_addr, UVM_ALL_ON | UVM_HEX)
    `uvm_object_utils_end
    
    function new(string name = "agent_config");
        super.new(name);
    endfunction
    
    function void post_randomize();
        if (max_delay < min_delay) begin
            `uvm_warning("CONFIG", "max_delay < min_delay, swapping")
            int tmp = max_delay;
            max_delay = min_delay;
            min_delay = tmp;
        end
    endfunction
endclass

class transaction extends uvm_sequence_item;
    rand bit [31:0] addr;
    rand bit [31:0] data;
    
    `uvm_object_utils_begin(transaction)
        `uvm_field_int(addr, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(data, UVM_ALL_ON | UVM_HEX)
    `uvm_object_utils_end
    
    function new(string name = "transaction");
        super.new(name);
    endfunction
endclass

// Driver using configuration
class configured_driver extends uvm_driver#(transaction);
    `uvm_component_utils(configured_driver)
    
    agent_config cfg;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        if (!uvm_config_db#(agent_config)::get(this, "", "cfg", cfg))
            `uvm_fatal(get_type_name(), "Config not found")
    endfunction
    
    task run_phase(uvm_phase phase);
        transaction tr;
        int delay;
        
        forever begin
            seq_item_port.get_next_item(tr);
            
            // Use config for delay
            delay = $urandom_range(cfg.min_delay, cfg.max_delay);
            `uvm_info(get_type_name(), $sformatf("Waiting %0d cycles", delay), UVM_HIGH)
            repeat(delay) #10ns;
            
            `uvm_info(get_type_name(), $sformatf("Driving: %s", tr.convert2string()), UVM_MEDIUM)
            
            seq_item_port.item_done();
        end
    endtask
endclass

// Sequence using configuration
class configured_sequence extends uvm_sequence#(transaction);
    `uvm_object_utils(configured_sequence)
    
    agent_config cfg;
    
    function new(string name = "configured_sequence");
        super.new(name);
    endfunction
    
    task body();
        transaction tr;
        
        // Get config from sequencer's context
        if (!uvm_config_db#(agent_config)::get(m_sequencer, "", "cfg", cfg))
            `uvm_fatal(get_type_name(), "Config not found")
        
        `uvm_info(get_type_name(), $sformatf("Using address range 0x%0h - 0x%0h", 
                  cfg.start_addr, cfg.end_addr), UVM_MEDIUM)
        
        repeat(10) begin
            tr = transaction::type_id::create("tr");
            start_item(tr);
            assert(tr.randomize() with {
                addr inside {[cfg.start_addr:cfg.end_addr]};
            });
            finish_item(tr);
        end
    endtask
endclass

// Agent with configuration
class configured_agent extends uvm_agent;
    `uvm_component_utils(configured_agent)
    
    agent_config cfg;
    configured_driver driver;
    uvm_sequencer#(transaction) sequencer;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(agent_config)::get(this, "", "cfg", cfg)) begin
            `uvm_info(get_type_name(), "Using default config", UVM_MEDIUM)
            cfg = agent_config::type_id::create("cfg");
        end
        
        // Apply is_active from config
        is_active = cfg.is_active;
        
        if (is_active == UVM_ACTIVE) begin
            driver = configured_driver::type_id::create("driver", this);
            sequencer = uvm_sequencer#(transaction)::type_id::create("sequencer", this);
            
            // Pass config down to driver and sequencer
            uvm_config_db#(agent_config)::set(this, "driver", "cfg", cfg);
            uvm_config_db#(agent_config)::set(this, "sequencer", "cfg", cfg);
        end
    endfunction
    
    function void connect_phase(uvm_phase phase);
        if (is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    
    configured_agent agent;
    agent_config cfg;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        // Create and configure
        cfg = agent_config::type_id::create("cfg");
        cfg.is_active = UVM_ACTIVE;
        cfg.min_delay = 2;
        cfg.max_delay = 8;
        cfg.start_addr = 32'h1000;
        cfg.end_addr = 32'h1FFF;
        
        // Set config in database
        uvm_config_db#(agent_config)::set(this, "agent*", "cfg", cfg);
        
        // Create agent
        agent = configured_agent::type_id::create("agent", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        configured_sequence seq;
        
        phase.raise_objection(this);
        
        seq = configured_sequence::type_id::create("seq");
        seq.start(agent.sequencer);
        
        #500ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
