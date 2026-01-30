// ============================================================================
// test_callbacks.sv - Callbacks for Tests and Environments
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class env_callback extends uvm_callback;
    `uvm_object_utils(env_callback)
    
    function new(string name = "env_callback");
        super.new(name);
    endfunction
    
    virtual function void pre_configure();
    endfunction
    
    virtual function void post_configure();
    endfunction
endclass

class my_env extends uvm_env;
    `uvm_component_utils(my_env)
    `uvm_register_cb(my_env, env_callback)
    
    bit configured = 0;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void configure();
        `uvm_do_callbacks(my_env, env_callback, pre_configure())
        
        `uvm_info(get_type_name(), "Configuring environment", UVM_MEDIUM)
        configured = 1;
        
        `uvm_do_callbacks(my_env, env_callback, post_configure())
    endfunction
    
    function void start_of_simulation_phase(uvm_phase phase);
        configure();
    endfunction
endclass

class custom_config_callback extends env_callback;
    `uvm_object_utils(custom_config_callback)
    
    function new(string name = "custom_config_callback");
        super.new(name);
    endfunction
    
    function void pre_configure();
        `uvm_info("CALLBACK", "Setting up custom configuration", UVM_MEDIUM)
    endfunction
    
    function void post_configure();
        `uvm_info("CALLBACK", "Configuration complete", UVM_MEDIUM)
    endfunction
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    my_env env;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        custom_config_callback cfg_cb;
        
        env = my_env::type_id::create("env", this);
        
        // Register callback
        cfg_cb = custom_config_callback::type_id::create("cfg_cb");
        uvm_callbacks#(my_env, env_callback)::add(env, cfg_cb);
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
