// ============================================================================
// phase_jumping.sv - Advanced Phase Control (Jump, Drop)
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class error_injector extends uvm_component;
    `uvm_component_utils(error_injector)
    
    bit inject_error = 0;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task main_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Running main phase", UVM_MEDIUM)
        
        #50ns;
        
        if (inject_error) begin
            `uvm_error(get_type_name(), "Critical error detected!")
            
            // Jump to reset phase to recover
            `uvm_info(get_type_name(), "Jumping back to reset phase", UVM_LOW)
            phase.jump(uvm_reset_phase::get());
        end
        
        phase.drop_objection(this);
    endtask
    
    task reset_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Executing reset phase", UVM_MEDIUM)
        #20ns;
        phase.drop_objection(this);
    endtask
endclass

class phase_controller extends uvm_component;
    `uvm_component_utils(phase_controller)
    
    int reset_count = 0;
    int max_resets = 3;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void phase_started(uvm_phase phase);
        super.phase_started(phase);
        
        `uvm_info(get_type_name(), 
                 $sformatf("Phase started: %s", phase.get_name()),
                 UVM_HIGH)
        
        // Track reset phases
        if (phase.get_name() == "reset") begin
            reset_count++;
            `uvm_info(get_type_name(), 
                     $sformatf("Reset count: %0d", reset_count),
                     UVM_MEDIUM)
            
            if (reset_count >= max_resets) begin
                `uvm_fatal(get_type_name(), 
                          "Too many resets - aborting simulation")
            end
        end
    endfunction
    
    function void phase_ended(uvm_phase phase);
        super.phase_ended(phase);
        
        `uvm_info(get_type_name(), 
                 $sformatf("Phase ended: %s", phase.get_name()),
                 UVM_HIGH)
    endfunction
    
    task reset_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Controller: Reset phase", UVM_MEDIUM)
        #10ns;
        phase.drop_objection(this);
    endtask
    
    task configure_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Controller: Configure phase", UVM_MEDIUM)
        #15ns;
        phase.drop_objection(this);
    endtask
    
    task main_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Controller: Main phase", UVM_MEDIUM)
        #30ns;
        phase.drop_objection(this);
    endtask
endclass

// Component that can skip phases
class selective_component extends uvm_component;
    `uvm_component_utils(selective_component)
    
    bit skip_configure = 0;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void phase_ready_to_end(uvm_phase phase);
        super.phase_ready_to_end(phase);
        
        // Can delay phase end here
        if (phase.get_name() == "main") begin
            `uvm_info(get_type_name(), "Delaying main phase end", UVM_HIGH)
        end
    endfunction
    
    task reset_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Selective: Reset phase", UVM_MEDIUM)
        #10ns;
        phase.drop_objection(this);
    endtask
    
    task configure_phase(uvm_phase phase);
        if (!skip_configure) begin
            phase.raise_objection(this);
            `uvm_info(get_type_name(), "Selective: Configure phase", UVM_MEDIUM)
            #10ns;
            phase.drop_objection(this);
        end else begin
            `uvm_info(get_type_name(), "Selective: Skipping configure phase", UVM_MEDIUM)
        end
    endtask
    
    task main_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Selective: Main phase", UVM_MEDIUM)
        #20ns;
        phase.drop_objection(this);
    endtask
endclass

class env extends uvm_env;
    `uvm_component_utils(env)
    
    phase_controller controller;
    selective_component sel_comp;
    error_injector err_inj;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        controller = phase_controller::type_id::create("controller", this);
        sel_comp = selective_component::type_id::create("sel_comp", this);
        err_inj = error_injector::type_id::create("err_inj", this);
    endfunction
endclass

class phase_jump_test extends uvm_test;
    `uvm_component_utils(phase_jump_test)
    
    env environment;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        environment = env::type_id::create("environment", this);
        
        // Configure to inject error (causes phase jump)
        environment.err_inj.inject_error = 1;
    endfunction
    
    function void start_of_simulation_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "=== Phase Jumping Test ===", UVM_LOW)
        `uvm_info(get_type_name(), "Error will be injected, causing jump to reset", UVM_LOW)
    endfunction
endclass

class normal_test extends uvm_test;
    `uvm_component_utils(normal_test)
    
    env environment;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        environment = env::type_id::create("environment", this);
        
        // Normal execution - no phase jumps
        environment.err_inj.inject_error = 0;
    endfunction
    
    function void start_of_simulation_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "=== Normal Test (No Phase Jumps) ===", UVM_LOW)
    endfunction
endclass

module top;
    initial begin
        // Enable runtime phases
        uvm_config_db#(int)::set(null, "*", "enable_runtime_phases", 1);
        
        // Run: +UVM_TESTNAME=phase_jump_test
        // Or:  +UVM_TESTNAME=normal_test
        run_test();
    end
endmodule
