// ============================================================================
// coverage_driven_test.sv - Coverage-Driven Test Strategy
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class packet extends uvm_sequence_item;
    rand bit [7:0] addr;
    rand bit [1:0] size;
    rand bit [1:0] burst_type;
    
    constraint addr_c {addr inside {[0:255]};}
    
    `uvm_object_utils(packet)
    function new(string name = "packet");
        super.new(name);
    endfunction
endclass

// Coverage model with holes
class coverage_model extends uvm_subscriber#(packet);
    `uvm_component_utils(coverage_model)
    
    covergroup cg;
        cp_addr: coverpoint collected_pkt.addr {
            bins low = {[0:63]};
            bins mid = {[64:127]};
            bins high = {[128:191]};
            bins max = {[192:255]};
        }
        
        cp_size: coverpoint collected_pkt.size;
        cp_burst: coverpoint collected_pkt.burst_type;
        
        cross_addr_size: cross cp_addr, cp_size;
    endgroup
    
    packet collected_pkt;
    int sample_count;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        cg = new();
    endfunction
    
    function void write(packet pkt);
        collected_pkt = pkt;
        cg.sample();
        sample_count++;
    endfunction
    
    // Return list of uncovered bins
    function void get_coverage_holes();
        real addr_cov = cg.cp_addr.get_coverage();
        
        `uvm_info(get_type_name(), "=== Coverage Holes ===", UVM_LOW)
        
        // Check each bin
        if (cg.cp_addr.get_inst_coverage(,, "low") < 100.0)
            `uvm_info(get_type_name(), "HOLE: Low address range not fully covered", UVM_LOW)
        if (cg.cp_addr.get_inst_coverage(,, "mid") < 100.0)
            `uvm_info(get_type_name(), "HOLE: Mid address range not fully covered", UVM_LOW)
        if (cg.cp_addr.get_inst_coverage(,, "high") < 100.0)
            `uvm_info(get_type_name(), "HOLE: High address range not fully covered", UVM_LOW)
        if (cg.cp_addr.get_inst_coverage(,, "max") < 100.0)
            `uvm_info(get_type_name(), "HOLE: Max address range not fully covered", UVM_LOW)
    endfunction
    
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), $sformatf("Total Samples: %0d", sample_count), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Total Coverage: %0.2f%%", cg.get_coverage()), UVM_LOW)
        get_coverage_holes();
    endfunction
endclass

// Intelligent sequence that targets coverage holes
class coverage_driven_sequence extends uvm_sequence#(packet);
    `uvm_object_utils(coverage_driven_sequence)
    
    coverage_model cov_model;
    int max_iterations = 1000;
    real coverage_goal = 95.0;
    
    function new(string name = "coverage_driven_sequence");
        super.new(name);
    endfunction
    
    task body();
        packet pkt;
        int iteration = 0;
        real current_cov;
        
        `uvm_info(get_type_name(), "Starting coverage-driven generation", UVM_MEDIUM)
        
        while (iteration < max_iterations) begin
            current_cov = cov_model.cg.get_coverage();
            
            if (current_cov >= coverage_goal) begin
                `uvm_info(get_type_name(), 
                         $sformatf("Coverage goal reached: %0.2f%%", current_cov),
                         UVM_LOW)
                break;
            end
            
            pkt = packet::type_id::create("pkt");
            start_item(pkt);
            
            // Bias towards uncovered areas
            if (cov_model.cg.cp_addr.get_inst_coverage(,, "low") < 100.0) begin
                assert(pkt.randomize() with {addr inside {[0:63]};});
            end else if (cov_model.cg.cp_addr.get_inst_coverage(,, "mid") < 100.0) begin
                assert(pkt.randomize() with {addr inside {[64:127]};});
            end else if (cov_model.cg.cp_addr.get_inst_coverage(,, "high") < 100.0) begin
                assert(pkt.randomize() with {addr inside {[128:191]};});
            end else if (cov_model.cg.cp_addr.get_inst_coverage(,, "max") < 100.0) begin
                assert(pkt.randomize() with {addr inside {[192:255]};});
            end else begin
                // Fully random if all covered
                assert(pkt.randomize());
            end
            
            finish_item(pkt);
            iteration++;
            
            if (iteration % 100 == 0) begin
                `uvm_info(get_type_name(), 
                         $sformatf("Progress: %0d iterations, %0.2f%% coverage",
                                   iteration, current_cov),
                         UVM_MEDIUM)
            end
        end
        
        `uvm_info(get_type_name(), 
                 $sformatf("Completed: %0d iterations, final coverage: %0.2f%%",
                           iteration, cov_model.cg.get_coverage()),
                 UVM_LOW)
    endtask
endclass

// Basic random sequence for comparison
class random_sequence extends uvm_sequence#(packet);
    `uvm_object_utils(random_sequence)
    
    int num_packets = 1000;
    
    function new(string name = "random_sequence");
        super.new(name);
    endfunction
    
    task body();
        packet pkt;
        
        repeat(num_packets) begin
            pkt = packet::type_id::create("pkt");
            start_item(pkt);
            assert(pkt.randomize());
            finish_item(pkt);
        end
    endtask
endclass

class simple_monitor extends uvm_monitor;
    `uvm_component_utils(simple_monitor)
    uvm_analysis_port#(packet) ap;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        ap = new("ap", this);
    endfunction
endclass

class env extends uvm_env;
    `uvm_component_utils(env)
    
    simple_monitor monitor;
    coverage_model cov_model;
    uvm_sequencer#(packet) sequencer;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        monitor = simple_monitor::type_id::create("monitor", this);
        cov_model = coverage_model::type_id::create("cov_model", this);
        sequencer = uvm_sequencer#(packet)::type_id::create("sequencer", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        monitor.ap.connect(cov_model.analysis_export);
    endfunction
endclass

class coverage_driven_test extends uvm_test;
    `uvm_component_utils(coverage_driven_test)
    
    env environment;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        environment = env::type_id::create("environment", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        coverage_driven_sequence cov_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "=== Coverage-Driven Test ===", UVM_LOW)
        
        cov_seq = coverage_driven_sequence::type_id::create("cov_seq");
        cov_seq.cov_model = environment.cov_model;
        cov_seq.coverage_goal = 98.0;
        cov_seq.start(environment.sequencer);
        
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

class random_test extends uvm_test;
    `uvm_component_utils(random_test)
    
    env environment;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        environment = env::type_id::create("environment", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        random_sequence rand_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "=== Random Test (for comparison) ===", UVM_LOW)
        
        rand_seq = random_sequence::type_id::create("rand_seq");
        rand_seq.start(environment.sequencer);
        
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial begin
        // Run: +UVM_TESTNAME=coverage_driven_test
        // Or:  +UVM_TESTNAME=random_test
        run_test();
    end
endmodule
