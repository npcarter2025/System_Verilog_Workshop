// ============================================================================
// phase_objections.sv - Objections Across Multiple Phases
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class multi_phase_component extends uvm_component;
    `uvm_component_utils(multi_phase_component)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task reset_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Reset phase: Applying reset", UVM_MEDIUM)
        #20ns;
        phase.drop_objection(this);
    endtask
    
    task configure_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Configure phase: Programming registers", UVM_MEDIUM)
        #30ns;
        phase.drop_objection(this);
    endtask
    
    task main_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Main phase: Running test traffic", UVM_MEDIUM)
        #50ns;
        phase.drop_objection(this);
    endtask
    
    task shutdown_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Shutdown phase: Draining", UVM_MEDIUM)
        #10ns;
        phase.drop_objection(this);
    endtask
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    
    multi_phase_component comp;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        comp = multi_phase_component::type_id::create("comp", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        // run_phase contains reset/configure/main/shutdown sub-phases
        `uvm_info(get_type_name(), "Test run_phase", UVM_LOW)
    endtask
    
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Test complete - all phases executed", UVM_LOW)
    endfunction
endclass

module top;
    initial begin
        // Enable run-time phases
        uvm_config_db#(int)::set(null, "*", "enable_runtime_phases", 1);
        run_test("test");
    end
endmodule
