// ============================================================================
// type_override.sv - Type-based Factory Overrides
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

class priority_packet extends packet;
    rand bit [2:0] priority;
    `uvm_object_utils(priority_packet)
    function new(string name = "priority_packet");
        super.new(name);
    endfunction
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        // Type override - affects ALL instances
        packet::type_id::set_type_override(priority_packet::get_type());
        `uvm_info(get_type_name(), "Type override: packet -> priority_packet", UVM_LOW)
    endfunction
    
    task run_phase(uvm_phase phase);
        packet pkt1, pkt2, pkt3;
        
        phase.raise_objection(this);
        
        // All three will be priority_packets due to type override
        pkt1 = packet::type_id::create("pkt1");
        pkt2 = packet::type_id::create("pkt2");
        pkt3 = packet::type_id::create("pkt3");
        
        `uvm_info(get_type_name(), $sformatf("pkt1 type: %s", pkt1.get_type_name()), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("pkt2 type: %s", pkt2.get_type_name()), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("pkt3 type: %s", pkt3.get_type_name()), UVM_LOW)
        
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
