// ============================================================================
// config_db_usage.sv - UVM Config DB Examples
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// Configuration object
class my_config extends uvm_object;
    int id;
    string name;
    bit [31:0] base_addr;
    
    `uvm_object_utils_begin(my_config)
        `uvm_field_int(id, UVM_ALL_ON)
        `uvm_field_string(name, UVM_ALL_ON)
        `uvm_field_int(base_addr, UVM_ALL_ON | UVM_HEX)
    `uvm_object_utils_end
    
    function new(string name = "my_config");
        super.new(name);
    endfunction
endclass

class component_a extends uvm_component;
    `uvm_component_utils(component_a)
    
    int my_int;
    string my_string;
    my_config cfg;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get integer value
        if (!uvm_config_db#(int)::get(this, "", "my_int", my_int))
            my_int = 100;  // default
        
        // Get string value
        if (!uvm_config_db#(string)::get(this, "", "my_string", my_string))
            my_string = "default";
        
        // Get config object
        if (!uvm_config_db#(my_config)::get(this, "", "cfg", cfg))
            `uvm_warning(get_type_name(), "Config not found")
        
        `uvm_info(get_type_name(), $sformatf("my_int=%0d my_string=%s", my_int, my_string), UVM_LOW)
        if (cfg != null)
            cfg.print();
    endfunction
endclass

class component_b extends uvm_component;
    `uvm_component_utils(component_b)
    
    real my_real;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        if (!uvm_config_db#(real)::get(this, "", "my_real", my_real))
            my_real = 3.14;
        
        `uvm_info(get_type_name(), $sformatf("my_real=%f", my_real), UVM_LOW)
    endfunction
endclass

class my_env extends uvm_env;
    `uvm_component_utils(my_env)
    
    component_a comp_a;
    component_b comp_b;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Set config for component_a
        uvm_config_db#(int)::set(this, "comp_a", "my_int", 42);
        uvm_config_db#(string)::set(this, "comp_a", "my_string", "hello");
        
        // Set config for component_b
        uvm_config_db#(real)::set(this, "comp_b", "my_real", 2.71828);
        
        // Create components
        comp_a = component_a::type_id::create("comp_a", this);
        comp_b = component_b::type_id::create("comp_b", this);
    endfunction
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    
    my_env env;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        my_config cfg;
        
        // Create and set configuration object
        cfg = my_config::type_id::create("cfg");
        cfg.id = 1;
        cfg.name = "test_config";
        cfg.base_addr = 32'h1000_0000;
        
        // Set with wildcard - applies to all matching components
        uvm_config_db#(my_config)::set(this, "*", "cfg", cfg);
        
        // Can also set globally (from null context)
        uvm_config_db#(int)::set(null, "uvm_test_top.*", "my_int", 999);
        
        env = my_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        #100ns;
        phase.drop_objection(this);
    endtask
    
    function void end_of_elaboration_phase(uvm_phase phase);
        // Print config_db contents
        `uvm_info(get_type_name(), "Config DB dump:", UVM_LOW)
        uvm_config_db#(int)::dump();
    endfunction
endclass

module top;
    initial run_test("test");
endmodule
