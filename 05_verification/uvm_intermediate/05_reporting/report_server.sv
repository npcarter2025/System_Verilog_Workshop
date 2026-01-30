// ============================================================================
// report_server.sv - Report Server Configuration
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class test extends uvm_test;
    `uvm_component_utils(test)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        uvm_report_server svr;
        svr = uvm_report_server::get_server();
        
        // Configure report server
        svr.set_max_quit_count(5);  // Stop after 5 fatals/errors
        svr.set_id_action("SPECIFIC_ID", UVM_DISPLAY | UVM_LOG);
        svr.set_id_verbosity("DEBUG_ID", UVM_DEBUG);
        
        // Configure component-specific reporting
        set_report_severity_action(UVM_ERROR, UVM_DISPLAY | UVM_COUNT);
        set_report_id_action("IGNORE_ME", UVM_NO_ACTION);
        set_report_id_verbosity("VERBOSE_ID", UVM_HIGH);
        
        `uvm_info(get_type_name(), "Report server configured", UVM_LOW)
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        // Test messages
        `uvm_info("NORMAL_ID", "Normal info message", UVM_MEDIUM)
        `uvm_info("VERBOSE_ID", "This should appear with high verbosity", UVM_HIGH)
        `uvm_info("SPECIFIC_ID", "This has custom actions", UVM_MEDIUM)
        `uvm_warning("IGNORE_ME", "This should be ignored")
        `uvm_error("NORMAL_ERROR", "This is an error")
        
        #100ns;
        phase.drop_objection(this);
    endtask
    
    function void report_phase(uvm_phase phase);
        uvm_report_server svr = uvm_report_server::get_server();
        
        `uvm_info(get_type_name(), "=== Test Summary ===", UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("FATAL: %0d", svr.get_severity_count(UVM_FATAL)), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("ERROR: %0d", svr.get_severity_count(UVM_ERROR)), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("WARNING: %0d", svr.get_severity_count(UVM_WARNING)), UVM_LOW)
        
        if (svr.get_severity_count(UVM_FATAL) + svr.get_severity_count(UVM_ERROR) == 0)
            `uvm_info(get_type_name(), "*** TEST PASSED ***", UVM_NONE)
        else
            `uvm_error(get_type_name(), "*** TEST FAILED ***")
    endfunction
endclass

module top;
    initial run_test("test");
endmodule
