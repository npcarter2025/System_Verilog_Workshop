// ============================================================================
// test_objections.sv - UVM Objection Mechanism
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class component_a extends uvm_component;
    `uvm_component_utils(component_a)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this, "component_a starting");
        `uvm_info(get_type_name(), "Working... (50ns)", UVM_MEDIUM)
        #50ns;
        phase.drop_objection(this, "component_a done");
    endtask
endclass

class component_b extends uvm_component;
    `uvm_component_utils(component_b)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this, "component_b starting");
        `uvm_info(get_type_name(), "Working... (100ns)", UVM_MEDIUM)
        #100ns;
        phase.drop_objection(this, "component_b done");
    endtask
endclass

// Component that raises/drops multiple times
class component_c extends uvm_component;
    `uvm_component_utils(component_c)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        // Multiple raise/drop cycles
        repeat(3) begin
            phase.raise_objection(this, "component_c iteration");
            `uvm_info(get_type_name(), "Processing...", UVM_MEDIUM)
            #30ns;
            phase.drop_objection(this, "component_c iteration done");
            #10ns;
        end
    endtask
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
        comp_a = component_a::type_id::create("comp_a", this);
        comp_b = component_b::type_id::create("comp_b", this);
        comp_c = component_c::type_id::create("comp_c", this);
    endfunction
    
    function void start_of_simulation_phase(uvm_phase phase);
        uvm_objection obj = phase.get_objection();
        obj.set_report_verbosity_level(UVM_HIGH);
    endfunction
    
    task run_phase(uvm_phase phase);
        // Test doesn't raise objection - components do
        // Simulation will end when all component objections are dropped
        `uvm_info(get_type_name(), "Test started - waiting for components", UVM_LOW)
    endtask
    
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "All objections dropped - test complete", UVM_LOW)
    endfunction
endclass

module top;
    initial run_test("test");
endmodule
