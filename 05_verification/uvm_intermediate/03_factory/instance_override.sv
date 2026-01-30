// ============================================================================
// instance_override.sv - Instance-based Factory Overrides
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class packet extends uvm_sequence_item;
    rand bit [7:0] data;
    `uvm_object_utils(packet)
    function new(string name = "packet");
        super.new(name);
    endfunction
endclass

class special_packet extends packet;
    rand bit [15:0] extra_data;
    `uvm_object_utils(special_packet)
    function new(string name = "special_packet");
        super.new(name);
    endfunction
endclass

class my_component extends uvm_component;
    `uvm_component_utils(my_component)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        packet pkt;
        
        phase.raise_objection(this);
        
        pkt = packet::type_id::create("pkt");
        `uvm_info(get_type_name(), $sformatf("Created: %s", pkt.get_type_name()), UVM_LOW)
        
        phase.drop_objection(this);
    endtask
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    
    my_component comp1, comp2, comp3;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        // Instance override - only affects specific instance
        packet::type_id::set_inst_override(special_packet::get_type(), 
                                           "comp2.pkt");
        
        `uvm_info(get_type_name(), "Instance override: comp2.pkt -> special_packet", UVM_LOW)
        
        comp1 = my_component::type_id::create("comp1", this);
        comp2 = my_component::type_id::create("comp2", this);
        comp3 = my_component::type_id::create("comp3", this);
    endfunction
endclass

module top;
    initial run_test("test");
endmodule
