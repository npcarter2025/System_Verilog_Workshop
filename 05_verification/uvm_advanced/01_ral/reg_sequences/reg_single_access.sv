// ============================================================================
// reg_single_access.sv - Single Register Access Sequences
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// Write then read back sequence
class write_read_sequence extends uvm_reg_sequence#(uvm_sequence#(uvm_reg_item));
    `uvm_object_utils(write_read_sequence)
    
    uvm_reg target_reg;
    rand uvm_reg_data_t write_data;
    uvm_reg_data_t read_data;
    
    function new(string name = "write_read_sequence");
        super.new(name);
    endfunction
    
    task body();
        uvm_status_e status;
        
        `uvm_info(get_type_name(), $sformatf("Writing 0x%0h to %s", 
                  write_data, target_reg.get_name()), UVM_MEDIUM)
        
        // Write
        target_reg.write(status, write_data, .parent(this));
        
        if (status != UVM_IS_OK)
            `uvm_error(get_type_name(), "Write failed")
        
        // Read back
        target_reg.read(status, read_data, .parent(this));
        
        if (status != UVM_IS_OK)
            `uvm_error(get_type_name(), "Read failed")
        
        `uvm_info(get_type_name(), $sformatf("Read back: 0x%0h", read_data), UVM_MEDIUM)
        
        // Compare
        if (read_data != write_data)
            `uvm_error(get_type_name(), $sformatf("Mismatch! Wrote 0x%0h, Read 0x%0h",
                      write_data, read_data))
    endtask
endclass

// Example: Would be used with actual register model
class test extends uvm_test;
    `uvm_component_utils(test)
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "RAL single access sequence template", UVM_LOW)
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
