// ============================================================================
// phase_example.sv - Complete UVM Phase Flow
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class phase_component extends uvm_component;
    `uvm_component_utils(phase_component)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        `uvm_info(get_type_name(), "new() - Constructor", UVM_HIGH)
    endfunction
    
    // BUILD PHASES (bottom-up execution)
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(get_type_name(), "build_phase() - Create sub-components", UVM_MEDIUM)
    endfunction
    
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info(get_type_name(), "connect_phase() - Connect TLM ports", UVM_MEDIUM)
    endfunction
    
    function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        `uvm_info(get_type_name(), "end_of_elaboration_phase() - Final checks", UVM_MEDIUM)
    endfunction
    
    function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info(get_type_name(), "start_of_simulation_phase() - Setup complete", UVM_MEDIUM)
    endfunction
    
    // RUN PHASE (parallel execution)
    
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "run_phase() - Main execution", UVM_MEDIUM)
        
        phase.raise_objection(this);
        #50ns;
        phase.drop_objection(this);
    endtask
    
    // Alternative: Fine-grained run-time phases
    
    task reset_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "reset_phase() - Apply reset", UVM_HIGH)
    endtask
    
    task configure_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "configure_phase() - Configure DUT", UVM_HIGH)
    endtask
    
    task main_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "main_phase() - Main test activity", UVM_HIGH)
    endtask
    
    task shutdown_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "shutdown_phase() - Cleanup", UVM_HIGH)
    endtask
    
    // CLEANUP PHASES (top-down execution)
    
    function void extract_phase(uvm_phase phase);
        super.extract_phase(phase);
        `uvm_info(get_type_name(), "extract_phase() - Extract coverage/data", UVM_MEDIUM)
    endfunction
    
    function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        `uvm_info(get_type_name(), "check_phase() - Check for errors", UVM_MEDIUM)
    endfunction
    
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info(get_type_name(), "report_phase() - Generate report", UVM_MEDIUM)
    endfunction
    
    function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        `uvm_info(get_type_name(), "final_phase() - Final cleanup", UVM_MEDIUM)
    endfunction
    
endclass

class my_env extends uvm_env;
    `uvm_component_utils(my_env)
    
    phase_component comp1;
    phase_component comp2;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        `uvm_info(get_type_name(), "ENV: new()", UVM_HIGH)
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(get_type_name(), "ENV: build_phase()", UVM_LOW)
        
        comp1 = phase_component::type_id::create("comp1", this);
        comp2 = phase_component::type_id::create("comp2", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info(get_type_name(), "ENV: connect_phase()", UVM_LOW)
    endfunction
    
    function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        `uvm_info(get_type_name(), "ENV: end_of_elaboration_phase()", UVM_LOW)
        `uvm_info(get_type_name(), "Testbench Topology:", UVM_LOW)
        this.print();
    endfunction
    
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "ENV: run_phase()", UVM_LOW)
        phase.raise_objection(this);
        #100ns;
        phase.drop_objection(this);
    endtask
    
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info(get_type_name(), "ENV: report_phase()", UVM_LOW)
    endfunction
endclass

class phase_test extends uvm_test;
    `uvm_component_utils(phase_test)
    
    my_env env;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        `uvm_info(get_type_name(), "TEST: new()", UVM_LOW)
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(get_type_name(), "==== BUILD PHASE ====", UVM_LOW)
        env = my_env::type_id::create("env", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info(get_type_name(), "==== CONNECT PHASE ====", UVM_LOW)
    endfunction
    
    function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        `uvm_info(get_type_name(), "==== END OF ELABORATION ====", UVM_LOW)
    endfunction
    
    function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info(get_type_name(), "==== START OF SIMULATION ====", UVM_LOW)
    endfunction
    
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "==== RUN PHASE ====", UVM_LOW)
        phase.raise_objection(this);
        #200ns;
        phase.drop_objection(this);
    endtask
    
    function void extract_phase(uvm_phase phase);
        super.extract_phase(phase);
        `uvm_info(get_type_name(), "==== EXTRACT PHASE ====", UVM_LOW)
    endfunction
    
    function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        `uvm_info(get_type_name(), "==== CHECK PHASE ====", UVM_LOW)
    endfunction
    
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info(get_type_name(), "==== REPORT PHASE ====", UVM_LOW)
        `uvm_info(get_type_name(), "Test Complete!", UVM_LOW)
    endfunction
    
    function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        `uvm_info(get_type_name(), "==== FINAL PHASE ====", UVM_LOW)
    endfunction
endclass

module top;
    initial run_test("phase_test");
endmodule

/*
EXPECTED PHASE ORDER:

1. build_phase (bottom-up: test -> env -> components)
2. connect_phase (bottom-up)
3. end_of_elaboration_phase (bottom-up)
4. start_of_simulation_phase (bottom-up)
5. run_phase (all in parallel)
   - OR fine-grained: reset, configure, main, shutdown (sequential)
6. extract_phase (top-down: components -> env -> test)
7. check_phase (top-down)
8. report_phase (top-down)
9. final_phase (top-down)
*/
