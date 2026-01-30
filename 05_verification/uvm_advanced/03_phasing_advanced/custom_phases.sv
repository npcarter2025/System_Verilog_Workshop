// ============================================================================
// custom_phases.sv - Custom Phase Definitions
// ============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// Define custom task phases
class initialization_phase extends uvm_task_phase;
    function new(string name = "initialization");
        super.new(name);
    endfunction
    
    static function initialization_phase get();
        static initialization_phase m_inst;
        if (m_inst == null)
            m_inst = new();
        return m_inst;
    endfunction
    
    virtual task exec_task(uvm_component comp, uvm_phase phase);
        initialization_interface intf;
        
        if ($cast(intf, comp)) begin
            intf.initialization_phase(phase);
        end
    endtask
endclass

class calibration_phase extends uvm_task_phase;
    function new(string name = "calibration");
        super.new(name);
    endfunction
    
    static function calibration_phase get();
        static calibration_phase m_inst;
        if (m_inst == null)
            m_inst = new();
        return m_inst;
    endfunction
    
    virtual task exec_task(uvm_component comp, uvm_phase phase);
        calibration_interface intf;
        
        if ($cast(intf, comp)) begin
            intf.calibration_phase(phase);
        end
    endtask
endclass

class traffic_generation_phase extends uvm_task_phase;
    function new(string name = "traffic_generation");
        super.new(name);
    endfunction
    
    static function traffic_generation_phase get();
        static traffic_generation_phase m_inst;
        if (m_inst == null)
            m_inst = new();
        return m_inst;
    endfunction
    
    virtual task exec_task(uvm_component comp, uvm_phase phase);
        traffic_interface intf;
        
        if ($cast(intf, comp)) begin
            intf.traffic_generation_phase(phase);
        end
    endtask
endclass

// Custom phase schedule
class custom_phase_schedule extends uvm_phase;
    function new(string name = "custom_schedule");
        super.new(name, UVM_PHASE_SCHEDULE);
    endfunction
    
    static function custom_phase_schedule build();
        custom_phase_schedule schedule = new();
        uvm_domain custom_domain = new("custom_domain");
        
        // Build custom phase sequence
        schedule.add(initialization_phase::get());
        schedule.add(calibration_phase::get());
        schedule.add(traffic_generation_phase::get());
        
        return schedule;
    endfunction
endclass

// Interfaces for custom phases
virtual class initialization_interface;
    pure virtual task initialization_phase(uvm_phase phase);
endclass

virtual class calibration_interface;
    pure virtual task calibration_phase(uvm_phase phase);
endclass

virtual class traffic_interface;
    pure virtual task traffic_generation_phase(uvm_phase phase);
endclass

// Component using custom phases
class custom_component extends uvm_component 
    implements initialization_interface, 
               calibration_interface,
               traffic_interface;
    
    `uvm_component_utils(custom_component)
    
    int calibration_value;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    // Custom phase implementations
    virtual task initialization_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "=== Initialization Phase ===", UVM_LOW)
        `uvm_info(get_type_name(), "Setting up hardware interfaces", UVM_MEDIUM)
        
        #20ns;  // Simulate initialization time
        
        phase.drop_objection(this);
    endtask
    
    virtual task calibration_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "=== Calibration Phase ===", UVM_LOW)
        `uvm_info(get_type_name(), "Calibrating system parameters", UVM_MEDIUM)
        
        // Simulate calibration
        repeat(5) begin
            calibration_value = $urandom_range(100, 200);
            `uvm_info(get_type_name(), 
                     $sformatf("Calibration iteration: value=%0d", calibration_value),
                     UVM_HIGH)
            #10ns;
        end
        
        `uvm_info(get_type_name(), 
                 $sformatf("Calibration complete: final_value=%0d", calibration_value),
                 UVM_MEDIUM)
        
        phase.drop_objection(this);
    endtask
    
    virtual task traffic_generation_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "=== Traffic Generation Phase ===", UVM_LOW)
        `uvm_info(get_type_name(), "Generating test traffic", UVM_MEDIUM)
        
        repeat(10) begin
            `uvm_info(get_type_name(), "Sending packet", UVM_HIGH)
            #5ns;
        end
        
        phase.drop_objection(this);
    endtask
    
    // Standard UVM phases still work
    function void build_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Standard build phase", UVM_MEDIUM)
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Standard run phase", UVM_MEDIUM)
        #10ns;
        phase.drop_objection(this);
    endtask
endclass

// Another component with different custom phase behavior
class sensor_component extends uvm_component 
    implements initialization_interface,
               calibration_interface;
    
    `uvm_component_utils(sensor_component)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    virtual task initialization_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Sensor initialization", UVM_MEDIUM)
        #15ns;
        phase.drop_objection(this);
    endtask
    
    virtual task calibration_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Sensor calibration", UVM_MEDIUM)
        #25ns;
        phase.drop_objection(this);
    endtask
endclass

class env extends uvm_env;
    `uvm_component_utils(env)
    
    custom_component comp1;
    custom_component comp2;
    sensor_component sensor;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        comp1 = custom_component::type_id::create("comp1", this);
        comp2 = custom_component::type_id::create("comp2", this);
        sensor = sensor_component::type_id::create("sensor", this);
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
    
    function void start_of_simulation_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "=== Custom Phases Test ===", UVM_LOW)
        `uvm_info(get_type_name(), "Demonstrates user-defined phase execution", UVM_LOW)
    endfunction
    
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "All custom phases completed successfully", UVM_LOW)
    endfunction
endclass

module top;
    initial begin
        // Note: Custom phase schedule would need to be registered
        // with UVM domain in a real implementation
        
        // For this example, we'll use standard phases
        // but demonstrate the custom phase interface pattern
        
        run_test("test");
    end
endmodule

/*
 * NOTES ON CUSTOM PHASES:
 * 
 * 1. Custom phases allow domain-specific verification flow
 * 2. Phases execute in defined order
 * 3. Components can implement only relevant phases
 * 4. Standard phases (build, connect, run, etc.) still available
 * 5. Custom domains can have different phase schedules
 * 
 * Use cases:
 * - Hardware bring-up sequences
 * - Multi-stage calibration
 * - Specialized test flows
 * - Domain-specific verification methodologies
 */
