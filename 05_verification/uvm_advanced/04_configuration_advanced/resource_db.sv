// ============================================================================
// resource_db.sv - UVM Resource Database (Alternative to Config DB)
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

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
    
    int shared_int;
    my_config cfg;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Resource DB lookup
        uvm_resource#(int) int_rsrc;
        uvm_resource#(my_config) cfg_rsrc;
        
        // Method 1: Using read_by_name
        if (uvm_resource_db#(int)::read_by_name(get_full_name(), "shared_int", shared_int)) begin
            `uvm_info(get_type_name(), $sformatf("Got shared_int=%0d from resource_db", shared_int), UVM_LOW)
        end else begin
            shared_int = 42;  // default
            `uvm_info(get_type_name(), "Using default shared_int=42", UVM_LOW)
        end
        
        // Method 2: Using get_by_name
        cfg_rsrc = uvm_resource_db#(my_config)::get_by_name(get_full_name(), "config");
        if (cfg_rsrc != null) begin
            cfg = cfg_rsrc.read();
            `uvm_info(get_type_name(), "Got config from resource_db", UVM_LOW)
            cfg.print();
        end else begin
            `uvm_info(get_type_name(), "No config found in resource_db", UVM_LOW)
        end
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        // Modify and write back to resource DB
        shared_int += 10;
        uvm_resource_db#(int)::set(get_full_name(), "modified_int", shared_int);
        `uvm_info(get_type_name(), $sformatf("Wrote modified_int=%0d", shared_int), UVM_MEDIUM)
        
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

class component_b extends uvm_component;
    `uvm_component_utils(component_b)
    
    int modified_int;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        #50ns;  // Wait for component_a to write
        
        // Read modified value
        if (uvm_resource_db#(int)::read_by_name("*", "modified_int", modified_int)) begin
            `uvm_info(get_type_name(), $sformatf("Read modified_int=%0d", modified_int), UVM_LOW)
        end
        
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

// Component demonstrating resource priorities
class component_c extends uvm_component;
    `uvm_component_utils(component_c)
    
    int priority_value;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        uvm_resource#(int) rsrc;
        
        // Get highest priority resource
        rsrc = uvm_resource_db#(int)::get_by_name(get_full_name(), "priority_test");
        if (rsrc != null) begin
            priority_value = rsrc.read();
            `uvm_info(get_type_name(), 
                     $sformatf("Got priority_value=%0d (priority=%0d)", 
                              priority_value, rsrc.get_priority()),
                     UVM_LOW)
        end
    endfunction
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    
    component_a comp_a;
    component_b comp_b;
    component_c comp_c;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        my_config cfg;
        
        `uvm_info(get_type_name(), "=== Resource DB Example ===", UVM_LOW)
        
        // Set resources before building components
        uvm_resource_db#(int)::set("*", "shared_int", 100);
        
        // Create and set config object
        cfg = my_config::type_id::create("cfg");
        cfg.id = 1;
        cfg.name = "test_config";
        cfg.base_addr = 32'h1000_0000;
        uvm_resource_db#(my_config)::set("*", "config", cfg);
        
        // Demonstrate priority (higher priority = higher precedence)
        uvm_resource_db#(int)::set("*", "priority_test", 10, this);  // Default priority
        uvm_resource_db#(int)::set("*", "priority_test", 20, this, 100);  // High priority
        uvm_resource_db#(int)::set("*", "priority_test", 5, this, 50);   // Medium priority
        
        // Build components
        comp_a = component_a::type_id::create("comp_a", this);
        comp_b = component_b::type_id::create("comp_b", this);
        comp_c = component_c::type_id::create("comp_c", this);
    endfunction
    
    function void end_of_elaboration_phase(uvm_phase phase);
        // Dump resource DB contents
        `uvm_info(get_type_name(), "\n=== Resource DB Dump ===", UVM_LOW)
        uvm_resource_db#(int)::dump();
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        #200ns;
        phase.drop_objection(this);
    endtask
    
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Resource DB test complete", UVM_LOW)
    endfunction
endclass

module top;
    initial run_test("test");
endmodule

/*
 * RESOURCE DB vs CONFIG DB:
 * 
 * CONFIG DB:
 * - Hierarchical scoping
 * - Type-safe with generics
 * - Set/get paradigm
 * - Recommended for most cases
 * 
 * RESOURCE DB:
 * - Global scope with wildcard matching
 * - Priority-based resolution
 * - More flexible but less structured
 * - Useful for cross-hierarchy communication
 * - Can override by priority
 * 
 * WHEN TO USE RESOURCE DB:
 * 1. Need priority-based configuration
 * 2. Global resources shared across hierarchy
 * 3. Dynamic resource updates during simulation
 * 4. Cross-hierarchy data sharing
 * 
 * WHEN TO USE CONFIG DB:
 * 1. Component configuration (most cases)
 * 2. Hierarchical parameter passing
 * 3. Virtual interface distribution
 * 4. Type-safe settings
 */
