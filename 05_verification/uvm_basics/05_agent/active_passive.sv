// ============================================================================
// active_passive.sv - Active vs Passive Agent Configuration
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class transaction extends uvm_sequence_item;
    rand bit [7:0] data;
    `uvm_object_utils_begin(transaction)
        `uvm_field_int(data, UVM_ALL_ON)
    `uvm_object_utils_end
    function new(string name = "transaction");
        super.new(name);
    endfunction
endclass

// Agent with active/passive configuration
class configurable_agent extends uvm_agent;
    `uvm_component_utils(configurable_agent)
    
    uvm_driver#(transaction) driver;
    uvm_monitor monitor;
    uvm_sequencer#(transaction) sequencer;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Monitor is ALWAYS created (passive component)
        monitor = uvm_monitor::type_id::create("monitor", this);
        
        // Driver and sequencer only in ACTIVE mode
        if (get_is_active() == UVM_ACTIVE) begin
            `uvm_info(get_type_name(), "Building ACTIVE agent", UVM_LOW)
            driver = uvm_driver#(transaction)::type_id::create("driver", this);
            sequencer = uvm_sequencer#(transaction)::type_id::create("sequencer", this);
        end else begin
            `uvm_info(get_type_name(), "Building PASSIVE agent (monitor only)", UVM_LOW)
        end
    endfunction
    
    function void connect_phase(uvm_phase phase);
        if (get_is_active() == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction
endclass

// Environment with both active and passive agents
class multi_agent_env extends uvm_env;
    `uvm_component_utils(multi_agent_env)
    
    configurable_agent master_agent;
    configurable_agent slave_agent;
    configurable_agent monitor_agent;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Master: ACTIVE (drives stimulus)
        master_agent = configurable_agent::type_id::create("master_agent", this);
        master_agent.is_active = UVM_ACTIVE;
        
        // Slave: ACTIVE (responds to master)
        slave_agent = configurable_agent::type_id::create("slave_agent", this);
        slave_agent.is_active = UVM_ACTIVE;
        
        // Monitor: PASSIVE (only observes)
        monitor_agent = configurable_agent::type_id::create("monitor_agent", this);
        monitor_agent.is_active = UVM_PASSIVE;
    endfunction
    
    function void end_of_elaboration_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Environment topology:", UVM_LOW)
        this.print();
    endfunction
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    
    multi_agent_env env;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        env = multi_agent_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
