// ============================================================================
// custom_reporter.sv - Custom UVM Reporter
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// Custom report server
class custom_report_server extends uvm_report_server;
    
    int error_limit = 10;
    int errors_seen = 0;
    
    function new(string name = "custom_report_server");
        super.new(name);
    endfunction
    
    virtual function void report(
        uvm_severity severity,
        string name,
        string id,
        string message,
        int verbosity_level = UVM_MEDIUM,
        string filename = "",
        int line = 0,
        string context_name = "",
        bit is_from_uvm = 1'b1
    );
        // Count errors
        if (severity == UVM_ERROR) begin
            errors_seen++;
            if (errors_seen >= error_limit) begin
                $display("*** ERROR LIMIT REACHED (%0d errors) - STOPPING ***", errors_seen);
                $finish;
            end
        end
        
        // Add timestamp to all messages
        message = $sformatf("[%0t] %s", $time, message);
        
        super.report(severity, name, id, message, verbosity_level, 
                    filename, line, context_name, is_from_uvm);
    endfunction
endclass

// Custom report catcher
class error_demoter extends uvm_report_catcher;
    
    function new(string name = "error_demoter");
        super.new(name);
    endfunction
    
    function action_e catch();
        // Demote specific errors to warnings
        if (get_severity() == UVM_ERROR && get_id() == "DEMOTE_ME") begin
            set_severity(UVM_WARNING);
            `uvm_info("CATCHER", "Demoted ERROR to WARNING", UVM_HIGH)
        end
        return THROW;
    endfunction
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        custom_report_server custom_svr;
        error_demoter catcher;
        
        // Install custom report server
        custom_svr = new("custom_svr");
        uvm_report_server::set_server(custom_svr);
        
        // Install report catcher
        catcher = new("catcher");
        uvm_report_cb::add(null, catcher);
        
        `uvm_info(get_type_name(), "Custom reporting installed", UVM_LOW)
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        // Generate various messages
        `uvm_info("TEST", "This is an info message", UVM_LOW)
        `uvm_warning("TEST", "This is a warning")
        
        // This error will be demoted to warning
        `uvm_error("DEMOTE_ME", "This error will be demoted")
        
        // Regular error
        `uvm_error("TEST", "This is a real error")
        
        #100ns;
        phase.drop_objection(this);
    endtask
    
    function void report_phase(uvm_phase phase);
        uvm_report_server svr;
        svr = uvm_report_server::get_server();
        
        `uvm_info(get_type_name(), "=== Final Report ===", UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Errors: %0d", svr.get_severity_count(UVM_ERROR)), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Warnings: %0d", svr.get_severity_count(UVM_WARNING)), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Info: %0d", svr.get_severity_count(UVM_INFO)), UVM_LOW)
    endfunction
endclass

module top;
    initial run_test("test");
endmodule
