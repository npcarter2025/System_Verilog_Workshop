// ============================================================================
// coverage_collector.sv - Coverage Collection and Analysis
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class transaction extends uvm_sequence_item;
    rand bit [7:0] addr;
    rand bit [31:0] data;
    rand bit [1:0] cmd;
    
    `uvm_object_utils_begin(transaction)
        `uvm_field_int(addr, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(data, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(cmd, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "transaction");
        super.new(name);
    endfunction
endclass

// Coverage collector as subscriber
class coverage_collector extends uvm_subscriber#(transaction);
    `uvm_component_utils(coverage_collector)
    
    // Coverage model
    covergroup cg_transaction;
        option.per_instance = 1;
        
        // Address coverage
        cp_addr: coverpoint collected_tr.addr {
            bins low_addr = {[0:63]};
            bins mid_addr = {[64:127]};
            bins high_addr = {[128:191]};
            bins max_addr = {[192:255]};
        }
        
        // Data coverage
        cp_data: coverpoint collected_tr.data {
            bins zero = {32'h0};
            bins small = {[32'h1:32'hFF]};
            bins medium = {[32'h100:32'hFFFF]};
            bins large = {[32'h10000:32'hFFFFFFFF]};
        }
        
        // Command coverage
        cp_cmd: coverpoint collected_tr.cmd {
            bins read = {2'b00};
            bins write = {2'b01};
            bins modify = {2'b10};
            illegal_bins invalid = {2'b11};
        }
        
        // Cross coverage
        cross_addr_cmd: cross cp_addr, cp_cmd {
            ignore_bins invalid_cross = binsof(cp_cmd.invalid);
        }
        
        // Transition coverage
        cp_addr_transitions: coverpoint collected_tr.addr {
            bins addr_seq = (0 => 1 => 2 => 3);
            bins addr_jump = (0 => 255);
        }
    endgroup
    
    transaction collected_tr;
    real previous_coverage;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        cg_transaction = new();
        previous_coverage = 0.0;
    endfunction
    
    // Called when transaction received via analysis port
    function void write(transaction t);
        collected_tr = t;
        cg_transaction.sample();
        
        real current_coverage = cg_transaction.get_coverage();
        
        `uvm_info(get_type_name(), 
                  $sformatf("Sampled: %s | Coverage: %0.2f%%", 
                            t.convert2string(), current_coverage),
                  UVM_HIGH)
        
        // Report when coverage increases
        if (current_coverage > previous_coverage) begin
            `uvm_info(get_type_name(),
                     $sformatf("Coverage increased: %0.2f%% -> %0.2f%%",
                               previous_coverage, current_coverage),
                     UVM_MEDIUM)
            previous_coverage = current_coverage;
        end
    endfunction
    
    function void report_phase(uvm_phase phase);
        real total_cov = cg_transaction.get_coverage();
        
        `uvm_info(get_type_name(), "=== Coverage Report ===", UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Total Coverage: %0.2f%%", total_cov), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Address Coverage: %0.2f%%", 
                  cg_transaction.cp_addr.get_coverage()), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Data Coverage: %0.2f%%",
                  cg_transaction.cp_data.get_coverage()), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Command Coverage: %0.2f%%",
                  cg_transaction.cp_cmd.get_coverage()), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Cross Coverage: %0.2f%%",
                  cg_transaction.cross_addr_cmd.get_coverage()), UVM_LOW)
        
        // Check coverage goals
        if (total_cov >= 95.0) begin
            `uvm_info(get_type_name(), "*** COVERAGE GOAL MET (95%) ***", UVM_NONE)
        end else begin
            `uvm_warning(get_type_name(), 
                        $sformatf("Coverage goal not met: %0.2f%% < 95%%", total_cov))
        end
    endfunction
    
    function void extract_phase(uvm_phase phase);
        // Could save coverage to file here
        `uvm_info(get_type_name(), "Coverage data extracted", UVM_LOW)
    endfunction
endclass

// Monitor to generate transactions
class simple_monitor extends uvm_monitor;
    `uvm_component_utils(simple_monitor)
    
    uvm_analysis_port#(transaction) ap;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        ap = new("ap", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        transaction tr;
        
        phase.raise_objection(this);
        
        // Generate random transactions
        repeat(100) begin
            tr = transaction::type_id::create("tr");
            assert(tr.randomize());
            
            ap.write(tr);
            #10ns;
        end
        
        phase.drop_objection(this);
    endtask
endclass

class env extends uvm_env;
    `uvm_component_utils(env)
    
    simple_monitor monitor;
    coverage_collector cov_collector;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        monitor = simple_monitor::type_id::create("monitor", this);
        cov_collector = coverage_collector::type_id::create("cov_collector", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        monitor.ap.connect(cov_collector.analysis_export);
    endfunction
endclass

class test extends uvm_test;
    `uvm_component_utils(test)
    
    env environment;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        environment = env::type_id::create("environment", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        #2000ns;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial begin
        // Enable coverage
        // +define+COVERAGE
        run_test("test");
    end
endmodule
