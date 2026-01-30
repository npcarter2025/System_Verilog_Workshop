// ============================================================================
// virtual_sequencer.sv - Virtual Sequencer and Virtual Sequences
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// Transactions for different interfaces
class bus_a_tr extends uvm_sequence_item;
    rand bit [7:0] data;
    `uvm_object_utils(bus_a_tr)
    function new(string name = "bus_a_tr");
        super.new(name);
    endfunction
endclass

class bus_b_tr extends uvm_sequence_item;
    rand bit [15:0] data;
    `uvm_object_utils(bus_b_tr)
    function new(string name = "bus_b_tr");
        super.new(name);
    endfunction
endclass

// Regular sequencers
typedef uvm_sequencer#(bus_a_tr) bus_a_sequencer;
typedef uvm_sequencer#(bus_b_tr) bus_b_sequencer;

// Virtual Sequencer - coordinates multiple sequencers
class virtual_sequencer extends uvm_sequencer;
    `uvm_component_utils(virtual_sequencer)
    
    // Handles to sub-sequencers
    bus_a_sequencer bus_a_seqr;
    bus_b_sequencer bus_b_seqr;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass

// Virtual Sequence - runs on virtual sequencer
class virtual_sequence extends uvm_sequence;
    `uvm_object_utils(virtual_sequence)
    `uvm_declare_p_sequencer(virtual_sequencer)
    
    function new(string name = "virtual_sequence");
        super.new(name);
    endfunction
    
    task body();
        bus_a_tr tr_a;
        bus_b_tr tr_b;
        
        `uvm_info(get_type_name(), "Starting virtual sequence", UVM_MEDIUM)
        
        // Coordinate activity on multiple interfaces
        fork
            // Send on bus A
            begin
                repeat(5) begin
                    tr_a = bus_a_tr::type_id::create("tr_a");
                    tr_a.start(p_sequencer.bus_a_seqr);
                end
            end
            
            // Send on bus B
            begin
                repeat(5) begin
                    tr_b = bus_b_tr::type_id::create("tr_b");
                    tr_b.start(p_sequencer.bus_b_seqr);
                end
            end
        join
        
        `uvm_info(get_type_name(), "Virtual sequence complete", UVM_MEDIUM)
    endtask
endclass

// Sequential virtual sequence
class sequential_virtual_sequence extends uvm_sequence;
    `uvm_object_utils(sequential_virtual_sequence)
    `uvm_declare_p_sequencer(virtual_sequencer)
    
    function new(string name = "sequential_virtual_sequence");
        super.new(name);
    endfunction
    
    task body();
        bus_a_tr tr_a;
        bus_b_tr tr_b;
        
        // First send on bus A
        `uvm_info(get_type_name(), "Sending on bus A", UVM_MEDIUM)
        repeat(3) begin
            tr_a = bus_a_tr::type_id::create("tr_a");
            tr_a.start(p_sequencer.bus_a_seqr);
        end
        
        // Then send on bus B
        `uvm_info(get_type_name(), "Sending on bus B", UVM_MEDIUM)
        repeat(3) begin
            tr_b = bus_b_tr::type_id::create("tr_b");
            tr_b.start(p_sequencer.bus_b_seqr);
        end
    endtask
endclass

// Environment
class my_env extends uvm_env;
    `uvm_component_utils(my_env)
    
    bus_a_sequencer bus_a_seqr;
    bus_b_sequencer bus_b_seqr;
    virtual_sequencer v_seqr;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        bus_a_seqr = bus_a_sequencer::type_id::create("bus_a_seqr", this);
        bus_b_seqr = bus_b_sequencer::type_id::create("bus_b_seqr", this);
        v_seqr = virtual_sequencer::type_id::create("v_seqr", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        // Connect sub-sequencers to virtual sequencer
        v_seqr.bus_a_seqr = bus_a_seqr;
        v_seqr.bus_b_seqr = bus_b_seqr;
    endfunction
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    my_env env;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        env = my_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        virtual_sequence vseq;
        sequential_virtual_sequence seq_vseq;
        
        phase.raise_objection(this);
        
        // Run parallel virtual sequence
        vseq = virtual_sequence::type_id::create("vseq");
        vseq.start(env.v_seqr);
        
        // Run sequential virtual sequence
        seq_vseq = sequential_virtual_sequence::type_id::create("seq_vseq");
        seq_vseq.start(env.v_seqr);
        
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
