// ============================================================================
// alu_test.sv - ALU UVM Test
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "alu_transaction.sv"

class alu_sequence extends uvm_sequence#(alu_transaction#(8));
    `uvm_object_utils(alu_sequence)
    
    function new(string name = "alu_sequence");
        super.new(name);
    endfunction
    
    task body();
        alu_transaction#(8) tr;
        
        // Test all operations
        for (int op = 0; op < 8; op++) begin
            repeat(5) begin
                tr = alu_transaction#(8)::type_id::create("tr");
                start_item(tr);
                assert(tr.randomize() with {tr.op == alu_op_e'(op);});
                finish_item(tr);
            end
        end
    endtask
endclass

class alu_test extends uvm_test;
    `uvm_component_utils(alu_test)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        alu_sequence seq;
        
        phase.raise_objection(this);
        
        seq = alu_sequence::type_id::create("seq");
        // seq.start(sequencer);  // Would start on sequencer in real testbench
        
        #1000ns;
        
        phase.drop_objection(this);
    endtask
endclass
