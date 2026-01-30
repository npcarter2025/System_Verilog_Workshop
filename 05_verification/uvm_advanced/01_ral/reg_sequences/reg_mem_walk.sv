// ============================================================================
// reg_mem_walk.sv - Memory Walking Pattern
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class mem_walk_sequence extends uvm_reg_sequence#(uvm_sequence#(uvm_reg_item));
    `uvm_object_utils(mem_walk_sequence)
    
    uvm_mem target_mem;
    
    function new(string name = "mem_walk_sequence");
        super.new(name);
    endfunction
    
    task body();
        uvm_status_e status;
        uvm_reg_data_t read_data;
        int size = target_mem.get_size();
        
        `uvm_info(get_type_name(), $sformatf("Memory walk on %s (%0d locations)",
                  target_mem.get_name(), size), UVM_MEDIUM)
        
        // Write incrementing pattern
        for (int i = 0; i < size; i++) begin
            target_mem.write(status, i, i, .parent(this));
        end
        
        // Read and verify
        for (int i = 0; i < size; i++) begin
            target_mem.read(status, i, read_data, .parent(this));
            if (read_data != i)
                `uvm_error(get_type_name(), $sformatf("Addr %0d: Expected %0d, Got %0d",
                          i, i, read_data))
        end
        
        `uvm_info(get_type_name(), "Memory walk complete", UVM_MEDIUM)
    endtask
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "RAL memory walk sequence template", UVM_LOW)
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
