# UVM Hello World

## Overview
This is your first UVM program! It demonstrates the absolute basics of UVM:
- How to import UVM
- How to create a test class
- How to use UVM phases
- How to start a UVM simulation

## Key Concepts

### 1. UVM Package Import
```systemverilog
`include "uvm_macros.svh"
import uvm_pkg::*;
```
- `uvm_macros.svh`: Provides utility macros like `` `uvm_info``
- `uvm_pkg`: Contains all UVM classes and functions

### 2. Test Class
```systemverilog
class hello_world_test extends uvm_test;
    `uvm_component_utils(hello_world_test)
```
- All tests extend `uvm_test`
- `` `uvm_component_utils`` registers the class with UVM factory

### 3. UVM Phases
UVM automatically calls these phases in order:

```
1. build_phase    - Construct components
2. connect_phase  - Connect components together
3. run_phase      - Main test execution (this is a task!)
4. extract_phase  - Extract data for checking
5. check_phase    - Check test results
6. report_phase   - Print final report
```

### 4. Objections
```systemverilog
phase.raise_objection(this);  // Keep simulation alive
// ... do work ...
phase.drop_objection(this);   // Allow simulation to end
```
- Without objections, simulation ends immediately
- Raise at start of run_phase, drop at end

### 5. UVM Info Messages
```systemverilog
`uvm_info(ID, MESSAGE, VERBOSITY)
```
Verbosity levels (most to least verbose):
- `UVM_DEBUG`: Very detailed debug info
- `UVM_HIGH`: High-detail info
- `UVM_MEDIUM`: Medium-detail info
- `UVM_LOW`: Low-detail info
- `UVM_NONE`: Always printed

## Files
- `hello_uvm.sv`: Complete working example
- `run.sh`: Script to compile and run

## Running the Example

### Using the provided script:
```bash
./run.sh
```

### Manual compilation (using QuestaSim):
```bash
# Compile
vlog -sv hello_uvm.sv +incdir+$UVM_HOME/src $UVM_HOME/src/uvm_pkg.sv

# Run with different verbosity levels
vsim -c top -do "run -all; quit" +UVM_VERBOSITY=UVM_LOW
vsim -c top -do "run -all; quit" +UVM_VERBOSITY=UVM_MEDIUM
vsim -c top -do "run -all; quit" +UVM_VERBOSITY=UVM_HIGH
```

### Using VCS:
```bash
vcs -sverilog -ntb_opts uvm-1.2 hello_uvm.sv
./simv +UVM_VERBOSITY=UVM_LOW
```

### Using Verilator (limited UVM support):
```bash
# Note: Verilator has limited UVM support
# Consider using a commercial simulator for full UVM features
```

## Expected Output
```
========================================
Starting UVM Hello World Example
========================================
UVM_INFO @ 0: uvm_test_top [hello_world_test] Constructor: Hello from new()
UVM_INFO @ 0: uvm_test_top [hello_world_test] Build Phase: Constructing testbench components
UVM_INFO @ 0: uvm_test_top [hello_world_test] Run Phase: Starting simulation
UVM_INFO @ 0: uvm_test_top [hello_world_test] **********************************
UVM_INFO @ 0: uvm_test_top [hello_world_test] *                                *
UVM_INFO @ 0: uvm_test_top [hello_world_test] *     HELLO WORLD FROM UVM!      *
UVM_INFO @ 0: uvm_test_top [hello_world_test] *                                *
UVM_INFO @ 0: uvm_test_top [hello_world_test] **********************************
UVM_INFO @ 100: uvm_test_top [hello_world_test] Run Phase: Simulation complete
UVM_INFO @ 100: uvm_test_top [hello_world_test] Report Phase: Test completed successfully!
```

## Exercises

### Exercise 1: Modify Verbosity
Try changing the verbosity levels of the `uvm_info` messages and observe which ones appear when you run with different `+UVM_VERBOSITY` settings.

### Exercise 2: Add More Phases
Add implementations for:
- `connect_phase()`
- `end_of_elaboration_phase()`
- `start_of_simulation_phase()`
- `extract_phase()`
- `check_phase()`

### Exercise 3: Multiple Messages
Add more `uvm_info` messages at different verbosity levels and experiment with the output.

### Exercise 4: Error Messages
Try these other message macros:
```systemverilog
`uvm_warning("TEST", "This is a warning")
`uvm_error("TEST", "This is an error")
// `uvm_fatal("TEST", "This is fatal")  // Stops simulation!
```

## Common Mistakes

### ❌ Forgetting to register with factory
```systemverilog
class my_test extends uvm_test;
    // Missing: `uvm_component_utils(my_test)
```

### ❌ Not raising/dropping objections
```systemverilog
task run_phase(uvm_phase phase);
    // Missing: phase.raise_objection(this);
    #100ns;
    // Missing: phase.drop_objection(this);
endtask
// Result: Simulation ends immediately!
```

### ❌ Wrong test name in run_test()
```systemverilog
run_test("wrong_name");  // Should be "hello_world_test"
```

### ❌ Function vs Task confusion
```systemverilog
function void run_phase(uvm_phase phase);  // WRONG! Should be task
```

## Next Steps
- **02_components**: Learn about UVM components (driver, monitor, sequencer)
- **03_transactions**: Create transaction objects
- **04_sequences**: Generate stimulus using sequences

## Additional Resources
- [UVM Cookbook](https://verificationacademy.com/cookbook/uvm)
- [UVM User Guide](https://www.accellera.org/images/downloads/standards/uvm/uvm_users_guide_1.2.pdf)
- [Verification Academy](https://verificationacademy.com)
