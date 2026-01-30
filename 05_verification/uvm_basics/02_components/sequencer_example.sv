// ============================================================================
// sequencer_example.sv - UVM Sequencer Component
// ============================================================================
// A sequencer is responsible for:
// 1. Managing the flow of transactions to the driver
// 2. Arbitrating between multiple sequences
// 3. Providing a TLM port for the driver to get transactions
//
// Key Concepts:
// - Usually just a typedef of uvm_sequencer
// - Can be extended for custom arbitration
// - Sequences run ON the sequencer
// - Driver gets transactions FROM the sequencer
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// ============================================================================
// TRANSACTION CLASS
// ============================================================================
class packet extends uvm_sequence_item;
    
    rand bit [7:0] src_addr;
    rand bit [7:0] dest_addr;
    rand bit [15:0] payload;
    rand int delay;  // delay before sending
    
    // Constraints
    constraint valid_delay_c {
        delay inside {[0:10]};
    }
    
    `uvm_object_utils_begin(packet)
        `uvm_field_int(src_addr, UVM_ALL_ON)
        `uvm_field_int(dest_addr, UVM_ALL_ON)
        `uvm_field_int(payload, UVM_ALL_ON)
        `uvm_field_int(delay, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "packet");
        super.new(name);
    endfunction
    
    function string convert2string();
        return $sformatf("src=0x%0h, dest=0x%0h, data=0x%0h, delay=%0d",
                         src_addr, dest_addr, payload, delay);
    endfunction
    
endclass

// ============================================================================
// BASIC SEQUENCER (typedef is sufficient for most cases)
// ============================================================================
typedef uvm_sequencer#(packet) packet_sequencer;

// ============================================================================
// CUSTOM SEQUENCER (with additional functionality)
// ============================================================================
class custom_sequencer extends uvm_sequencer#(packet);
    
    `uvm_component_utils(custom_sequencer)
    
    // Custom configuration
    int unsigned max_outstanding_reqs = 8;
    int unsigned current_outstanding = 0;
    
    function new(string name = "custom_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Override to add custom behavior
    task get_next_item(output REQ t);
        // Wait if too many outstanding requests
        while (current_outstanding >= max_outstanding_reqs) begin
            `uvm_info(get_type_name(), "Throttling: too many outstanding requests", UVM_HIGH)
            #10ns;
        end
        
        super.get_next_item(t);
        current_outstanding++;
        
        `uvm_info(get_type_name(), 
                  $sformatf("Dispatched packet (outstanding=%0d)", current_outstanding),
                  UVM_HIGH)
    endtask
    
    // Called when driver completes a transaction
    function void item_done(RSP t = null);
        super.item_done(t);
        current_outstanding--;
        `uvm_info(get_type_name(), 
                  $sformatf("Completed packet (outstanding=%0d)", current_outstanding),
                  UVM_HIGH)
    endfunction
    
endclass

// ============================================================================
// SIMPLE DRIVER (to consume packets)
// ============================================================================
class packet_driver extends uvm_driver#(packet);
    
    `uvm_component_utils(packet_driver)
    
    function new(string name = "packet_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        packet pkt;
        
        forever begin
            // Get packet from sequencer
            seq_item_port.get_next_item(pkt);
            
            `uvm_info(get_type_name(), 
                      $sformatf("Driving packet: %s", pkt.convert2string()),
                      UVM_MEDIUM)
            
            // Simulate driving delay
            #(pkt.delay * 10ns);
            
            // Done with packet
            seq_item_port.item_done();
        end
    endtask
    
endclass

// ============================================================================
// SEQUENCE EXAMPLES
// ============================================================================

// Base sequence (abstract)
class base_sequence extends uvm_sequence#(packet);
    
    `uvm_object_utils(base_sequence)
    
    function new(string name = "base_sequence");
        super.new(name);
    endfunction
    
    // Override in derived classes
    task body();
        `uvm_error(get_type_name(), "base_sequence::body() must be overridden!")
    endtask
    
endclass

// Simple sequence - sends N packets
class simple_sequence extends base_sequence;
    
    `uvm_object_utils(simple_sequence)
    
    int unsigned num_packets = 5;
    
    function new(string name = "simple_sequence");
        super.new(name);
    endfunction
    
    task body();
        packet pkt;
        
        `uvm_info(get_type_name(), 
                  $sformatf("Starting sequence: %0d packets", num_packets),
                  UVM_MEDIUM)
        
        repeat(num_packets) begin
            pkt = packet::type_id::create("pkt");
            
            start_item(pkt);
            
            if (!pkt.randomize()) begin
                `uvm_error(get_type_name(), "Randomization failed")
            end
            
            finish_item(pkt);
        end
        
        `uvm_info(get_type_name(), "Sequence complete", UVM_MEDIUM)
    endtask
    
endclass

// Directed sequence - specific values
class directed_sequence extends base_sequence;
    
    `uvm_object_utils(directed_sequence)
    
    bit [7:0] target_addr = 8'hFF;
    
    function new(string name = "directed_sequence");
        super.new(name);
    endfunction
    
    task body();
        packet pkt;
        
        `uvm_info(get_type_name(), 
                  $sformatf("Sending packet to target: 0x%0h", target_addr),
                  UVM_MEDIUM)
        
        pkt = packet::type_id::create("pkt");
        
        start_item(pkt);
        
        if (!pkt.randomize() with {
            dest_addr == target_addr;
            delay == 0;  // immediate
        }) begin
            `uvm_error(get_type_name(), "Randomization failed")
        end
        
        finish_item(pkt);
    endtask
    
endclass

// Parallel sequence - demonstrates sequence parallelism
class parallel_sequence extends base_sequence;
    
    `uvm_object_utils(parallel_sequence)
    
    simple_sequence seq1;
    simple_sequence seq2;
    
    function new(string name = "parallel_sequence");
        super.new(name);
    endfunction
    
    task body();
        `uvm_info(get_type_name(), "Starting parallel sequences", UVM_MEDIUM)
        
        seq1 = simple_sequence::type_id::create("seq1");
        seq2 = simple_sequence::type_id::create("seq2");
        
        seq1.num_packets = 3;
        seq2.num_packets = 3;
        
        // Run both sequences in parallel
        fork
            seq1.start(m_sequencer);
            seq2.start(m_sequencer);
        join
        
        `uvm_info(get_type_name(), "Parallel sequences complete", UVM_MEDIUM)
    endtask
    
endclass

// Sequential sequence - run sequences one after another
class sequential_sequence extends base_sequence;
    
    `uvm_object_utils(sequential_sequence)
    
    directed_sequence dir_seq;
    simple_sequence simple_seq;
    
    function new(string name = "sequential_sequence");
        super.new(name);
    endfunction
    
    task body();
        `uvm_info(get_type_name(), "Starting sequential sequences", UVM_MEDIUM)
        
        // First run directed sequence
        dir_seq = directed_sequence::type_id::create("dir_seq");
        dir_seq.target_addr = 8'hAA;
        dir_seq.start(m_sequencer);
        
        // Then run simple sequence
        simple_seq = simple_sequence::type_id::create("simple_seq");
        simple_seq.num_packets = 4;
        simple_seq.start(m_sequencer);
        
        `uvm_info(get_type_name(), "Sequential sequences complete", UVM_MEDIUM)
    endtask
    
endclass

// ============================================================================
// AGENT
// ============================================================================
class packet_agent extends uvm_agent;
    
    `uvm_component_utils(packet_agent)
    
    packet_driver driver;
    custom_sequencer sequencer;
    
    function new(string name = "packet_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        driver = packet_driver::type_id::create("driver", this);
        sequencer = custom_sequencer::type_id::create("sequencer", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        driver.seq_item_port.connect(sequencer.seq_item_export);
    endfunction
    
endclass

// ============================================================================
// TEST - Demonstrates different sequence usage patterns
// ============================================================================
class sequencer_test extends uvm_test;
    
    `uvm_component_utils(sequencer_test)
    
    packet_agent agent;
    
    function new(string name = "sequencer_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        agent = packet_agent::type_id::create("agent", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        simple_sequence simple_seq;
        directed_sequence dir_seq;
        parallel_sequence par_seq;
        sequential_sequence seq_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "=== Starting Sequencer Test ===", UVM_LOW)
        
        // Pattern 1: Simple sequence
        `uvm_info(get_type_name(), "\n--- Running Simple Sequence ---", UVM_LOW)
        simple_seq = simple_sequence::type_id::create("simple_seq");
        simple_seq.num_packets = 3;
        simple_seq.start(agent.sequencer);
        #100ns;
        
        // Pattern 2: Directed sequence
        `uvm_info(get_type_name(), "\n--- Running Directed Sequence ---", UVM_LOW)
        dir_seq = directed_sequence::type_id::create("dir_seq");
        dir_seq.target_addr = 8'h42;
        dir_seq.start(agent.sequencer);
        #100ns;
        
        // Pattern 3: Parallel sequences
        `uvm_info(get_type_name(), "\n--- Running Parallel Sequence ---", UVM_LOW)
        par_seq = parallel_sequence::type_id::create("par_seq");
        par_seq.start(agent.sequencer);
        #100ns;
        
        // Pattern 4: Sequential sequence (sequence of sequences)
        `uvm_info(get_type_name(), "\n--- Running Sequential Sequence ---", UVM_LOW)
        seq_seq = sequential_sequence::type_id::create("seq_seq");
        seq_seq.start(agent.sequencer);
        #100ns;
        
        phase.drop_objection(this);
        `uvm_info(get_type_name(), "\n=== Sequencer Test Complete ===", UVM_LOW)
    endtask
    
endclass

// ============================================================================
// TOP MODULE
// ============================================================================
module top;
    
    initial begin
        run_test("sequencer_test");
    end
    
    // Watchdog
    initial begin
        #10us;
        $display("Simulation timeout");
        $finish;
    end
    
endmodule
