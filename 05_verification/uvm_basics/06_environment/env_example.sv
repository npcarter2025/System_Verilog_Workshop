// ============================================================================
// env_example.sv - UVM Environment
// ============================================================================
// Environment contains all agents, scoreboards, and other verification
// components needed to verify the DUT
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class packet extends uvm_sequence_item;
    rand bit [7:0] data;
    `uvm_object_utils_begin(packet)
        `uvm_field_int(data, UVM_ALL_ON)
    `uvm_object_utils_end
    function new(string name = "packet");
        super.new(name);
    endfunction
endclass

class master_agent extends uvm_agent;
    `uvm_component_utils(master_agent)
    uvm_sequencer#(packet) sequencer;
    uvm_analysis_port#(packet) ap;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        sequencer = uvm_sequencer#(packet)::type_id::create("sequencer", this);
        ap = new("ap", this);
    endfunction
endclass

class slave_agent extends uvm_agent;
    `uvm_component_utils(slave_agent)
    uvm_analysis_port#(packet) ap;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        ap = new("ap", this);
    endfunction
endclass

class scoreboard extends uvm_scoreboard;
    `uvm_component_utils(scoreboard)
    
    uvm_analysis_export#(packet) expected_export;
    uvm_analysis_export#(packet) actual_export;
    
    uvm_tlm_analysis_fifo#(packet) expected_fifo;
    uvm_tlm_analysis_fifo#(packet) actual_fifo;
    
    int matches;
    int mismatches;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        expected_export = new("expected_export", this);
        actual_export = new("actual_export", this);
        expected_fifo = new("expected_fifo", this);
        actual_fifo = new("actual_fifo", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        expected_export.connect(expected_fifo.analysis_export);
        actual_export.connect(actual_fifo.analysis_export);
    endfunction
    
    task run_phase(uvm_phase phase);
        packet expected_pkt, actual_pkt;
        
        forever begin
            fork
                expected_fifo.get(expected_pkt);
                actual_fifo.get(actual_pkt);
            join
            
            if (expected_pkt.compare(actual_pkt)) begin
                matches++;
                `uvm_info(get_type_name(), "MATCH", UVM_HIGH)
            end else begin
                mismatches++;
                `uvm_error(get_type_name(), $sformatf("MISMATCH: expected=%0d actual=%0d",
                          expected_pkt.data, actual_pkt.data))
            end
        end
    endtask
    
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), $sformatf("Matches: %0d, Mismatches: %0d", 
                  matches, mismatches), UVM_LOW)
        if (mismatches > 0)
            `uvm_error(get_type_name(), "Test FAILED")
        else
            `uvm_info(get_type_name(), "Test PASSED", UVM_LOW)
    endfunction
endclass

// Full Environment
class my_env extends uvm_env;
    `uvm_component_utils(my_env)
    
    master_agent master_agt;
    slave_agent slave_agt;
    scoreboard sb;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        master_agt = master_agent::type_id::create("master_agt", this);
        slave_agt = slave_agent::type_id::create("slave_agt", this);
        sb = scoreboard::type_id::create("sb", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect agents to scoreboard
        master_agt.ap.connect(sb.expected_export);
        slave_agt.ap.connect(sb.actual_export);
    endfunction
    
    function void end_of_elaboration_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Environment topology:", UVM_LOW)
        this.print();
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
        phase.raise_objection(this);
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial run_test("test");
endmodule
