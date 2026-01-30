// ============================================================================
// reg_bit_bash.sv - Bit Bash Sequence (Tests Each Bit)
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class bit_bash_sequence extends uvm_reg_sequence#(uvm_sequence#(uvm_reg_item));
    `uvm_object_utils(bit_bash_sequence)
    
    uvm_reg target_reg;
    
    function new(string name = "bit_bash_sequence");
        super.new(name);
    endfunction
    
    task body();
        uvm_status_e status;
        uvm_reg_data_t read_data;
        int size = target_reg.get_n_bits();
        
        `uvm_info(get_type_name(), $sformatf("Bit bashing %s (%0d bits)",
                  target_reg.get_name(), size), UVM_MEDIUM)
        
        // Test walking 1s
        for (int i = 0; i < size; i++) begin
            uvm_reg_data_t pattern = (1 << i);
            
            target_reg.write(status, pattern, .parent(this));
            target_reg.read(status, read_data, .parent(this));
            
            if (read_data != pattern)
                `uvm_error(get_type_name(), $sformatf("Walking 1 failed at bit %0d", i))
        end
        
        // Test walking 0s
        for (int i = 0; i < size; i++) begin
            uvm_reg_data_t pattern = ~(1 << i);
            
            target_reg.write(status, pattern, .parent(this));
            target_reg.read(status, read_data, .parent(this));
            
            if (read_data != pattern)
                `uvm_error(get_type_name(), $sformatf("Walking 0 failed at bit %0d", i))
        end
        
        `uvm_info(get_type_name(), "Bit bash complete", UVM_MEDIUM)
    endtask
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "RAL bit bash sequence template", UVM_LOW)
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
