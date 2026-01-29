# 05 - Verification with UVM

This directory contains comprehensive coverage of SystemVerilog verification methodologies, with a primary focus on the **Universal Verification Methodology (UVM)**. Learn industry-standard verification techniques used in modern chip verification.

## Table of Contents

- [Overview](#overview)
- [Directory Structure](#directory-structure)
- [Why UVM?](#why-uvm)
- [UVM Basics](#uvm-basics)
- [UVM Architecture](#uvm-architecture)
- [Key Concepts](#key-concepts)
- [Advanced Topics](#advanced-topics)
- [Verification Best Practices](#verification-best-practices)
- [Learning Path](#learning-path)
- [References](#references)

---

## Overview

**Verification** is the process of ensuring that a design meets its specifications. Modern hardware verification is:
- **Constrained-random**: Not exhaustive testing, but intelligent sampling
- **Coverage-driven**: Measure what's been tested
- **Layered**: Separate test intent from low-level implementation
- **Reusable**: Build verification IPs (VIPs) once, use many times

**UVM (Universal Verification Methodology)** is the industry-standard framework built on SystemVerilog that provides:
- Standard architecture and base classes
- Testbench automation (phases, factory, config)
- Communication mechanisms (TLM)
- Register abstraction (RAL)

---

## Directory Structure

```
05_verification/
├── README.md                          # This file
├── uvm_basics/
│   ├── 01_hello_world/
│   │   ├── hello_uvm.sv
│   │   ├── README.md
│   │   └── run.sh
│   ├── 02_components/
│   │   ├── driver_example.sv
│   │   ├── monitor_example.sv
│   │   ├── sequencer_example.sv
│   │   └── README.md
│   ├── 03_transactions/
│   │   ├── transaction_class.sv
│   │   ├── field_macros_example.sv
│   │   └── README.md
│   ├── 04_sequences/
│   │   ├── base_sequence.sv
│   │   ├── directed_sequence.sv
│   │   ├── random_sequence.sv
│   │   └── README.md
│   ├── 05_agent/
│   │   ├── simple_agent.sv
│   │   ├── active_passive.sv
│   │   ├── config_object.sv
│   │   └── README.md
│   ├── 06_environment/
│   │   ├── env_example.sv
│   │   ├── config_db_usage.sv
│   │   └── README.md
│   ├── 07_test/
│   │   ├── base_test.sv
│   │   ├── test_variations.sv
│   │   └── README.md
│   ├── 08_phases/
│   │   ├── phase_example.sv
│   │   └── README.md
│   └── README.md
├── uvm_intermediate/
│   ├── 01_virtual_sequences/
│   │   ├── virtual_sequencer.sv
│   │   ├── multi_interface_seq.sv
│   │   └── README.md
│   ├── 02_callbacks/
│   │   ├── driver_callbacks.sv
│   │   ├── test_callbacks.sv
│   │   └── README.md
│   ├── 03_factory/
│   │   ├── factory_override.sv
│   │   ├── type_override.sv
│   │   ├── instance_override.sv
│   │   └── README.md
│   ├── 04_objections/
│   │   ├── test_objections.sv
│   │   ├── phase_objections.sv
│   │   └── README.md
│   ├── 05_reporting/
│   │   ├── custom_reporter.sv
│   │   ├── report_server.sv
│   │   └── README.md
│   ├── 06_tlm/
│   │   ├── tlm_ports.sv
│   │   ├── tlm_analysis_port.sv
│   │   ├── tlm_fifos.sv
│   │   └── README.md
│   └── README.md
├── uvm_advanced/
│   ├── 01_ral/                        # Register Abstraction Layer
│   │   ├── simple_reg_model/
│   │   │   ├── my_reg_block.sv
│   │   │   ├── reg_adapter.sv
│   │   │   ├── reg_predictor.sv
│   │   │   └── README.md
│   │   ├── reg_sequences/
│   │   │   ├── reg_single_access.sv
│   │   │   ├── reg_bit_bash.sv
│   │   │   ├── reg_mem_walk.sv
│   │   │   └── README.md
│   │   └── README.md
│   ├── 02_coverage_driven/
│   │   ├── coverage_collector.sv
│   │   ├── coverage_driven_test.sv
│   │   └── README.md
│   ├── 03_phasing_advanced/
│   │   ├── phase_jumping.sv
│   │   ├── custom_phases.sv
│   │   └── README.md
│   ├── 04_configuration_advanced/
│   │   ├── resource_db.sv
│   │   ├── config_patterns.sv
│   │   └── README.md
│   └── README.md
├── constrained_random/
│   ├── basic_constraints/
│   │   ├── simple_constraints.sv
│   │   ├── dist_constraints.sv       # Distribution weights
│   │   ├── implication.sv            # -> operator
│   │   ├── array_constraints.sv
│   │   └── README.md
│   ├── advanced_constraints/
│   │   ├── soft_constraints.sv
│   │   ├── solve_before.sv
│   │   ├── dynamic_constraints.sv    # constraint_mode
│   │   ├── inline_constraints.sv     # randomize() with {}
│   │   ├── pre_post_randomize.sv
│   │   └── README.md
│   ├── constraint_patterns/
│   │   ├── address_alignment.sv
│   │   ├── protocol_constraints.sv
│   │   ├── performance_constraints.sv
│   │   ├── exclusion_constraints.sv
│   │   └── README.md
│   └── README.md
├── functional_coverage/
│   ├── basic_coverage/
│   │   ├── covergroup_basics.sv
│   │   ├── coverpoint.sv
│   │   ├── bins_example.sv
│   │   └── README.md
│   ├── advanced_coverage/
│   │   ├── cross_coverage.sv
│   │   ├── transition_bins.sv
│   │   ├── illegal_bins.sv
│   │   ├── ignore_bins.sv
│   │   ├── per_instance_coverage.sv
│   │   └── README.md
│   ├── coverage_driven/
│   │   ├── coverage_feedback.sv
│   │   └── README.md
│   └── README.md
├── scoreboards/
│   ├── basic_scoreboard/
│   │   ├── fifo_scoreboard.sv        # In-order checking
│   │   └── README.md
│   ├── reorder_scoreboard/
│   │   ├── associative_array_sb.sv   # Out-of-order checking
│   │   └── README.md
│   ├── predictor/
│   │   ├── reference_model.sv
│   │   ├── predictor_scoreboard.sv
│   │   └── README.md
│   └── README.md
├── verification_ips/                  # Reusable VIPs
│   ├── apb_vip/
│   │   ├── apb_transaction.sv
│   │   ├── apb_driver.sv
│   │   ├── apb_monitor.sv
│   │   ├── apb_sequencer.sv
│   │   ├── apb_agent.sv
│   │   ├── apb_config.sv
│   │   ├── sequences/
│   │   │   ├── apb_base_seq.sv
│   │   │   ├── apb_write_seq.sv
│   │   │   ├── apb_read_seq.sv
│   │   │   └── apb_random_seq.sv
│   │   └── README.md
│   ├── axi_lite_vip/
│   │   └── ... (similar structure)
│   ├── uart_vip/
│   │   └── ...
│   └── README.md
├── testbench_patterns/
│   ├── layered_testbench/
│   │   └── README.md
│   ├── interface_based/
│   │   ├── interface_example.sv
│   │   ├── modport_usage.sv
│   │   └── README.md
│   ├── clocking_blocks/
│   │   ├── clocking_example.sv
│   │   └── README.md
│   └── README.md
├── debug_techniques/
│   ├── waveform_dump.sv
│   ├── transaction_recording.sv
│   ├── uvm_debug_messaging.sv
│   └── README.md
├── non_uvm_verification/              # Other methodologies
│   ├── basic_testbench/
│   │   ├── simple_tb.sv
│   │   └── README.md
│   ├── class_based_tb/
│   │   ├── mailbox_example.sv
│   │   ├── semaphore_example.sv
│   │   ├── event_example.sv
│   │   └── README.md
│   └── README.md
└── complete_examples/                 # Full working examples
    ├── simple_alu_uvm/
    │   ├── dut/
    │   │   └── alu.sv
    │   ├── tb/
    │   │   ├── alu_if.sv
    │   │   ├── alu_transaction.sv
    │   │   ├── alu_sequence.sv
    │   │   ├── alu_driver.sv
    │   │   ├── alu_monitor.sv
    │   │   ├── alu_agent.sv
    │   │   ├── alu_scoreboard.sv
    │   │   ├── alu_env.sv
    │   │   └── alu_test.sv
    │   ├── sim/
    │   │   ├── run.sh
    │   │   └── Makefile
    │   └── README.md
    ├── fifo_uvm/
    │   └── ...
    └── uart_uvm/
        └── ...
```

---

## Why UVM?

### The Verification Challenge

Modern chips have:
- **Billions of transistors**: Can't verify exhaustively
- **Complex protocols**: Need structured testing
- **Short time-to-market**: Reuse is critical
- **High quality requirements**: Bugs are expensive

### Traditional vs UVM Approach

| Aspect | Traditional | UVM |
|--------|-------------|-----|
| **Structure** | Ad-hoc | Standardized hierarchy |
| **Reuse** | Difficult | Built-in (VIPs) |
| **Stimulus** | Directed | Constrained-random |
| **Coverage** | Manual | Automated functional coverage |
| **Configuration** | Hardcoded | Config DB, factory |
| **Debug** | Printf debugging | Transaction recording, phases |

### UVM Benefits

1. **Standardization**: Everyone speaks same language
2. **Reusability**: Write once, use everywhere
3. **Scalability**: From block to chip level
4. **Automation**: Phases, factory, configuration
5. **Industry adoption**: Required skill for verification engineers

---

## UVM Basics

### UVM Component Hierarchy

```
test
└── env
    ├── agent_1 (active)
    │   ├── sequencer
    │   ├── driver
    │   └── monitor
    ├── agent_2 (passive)
    │   └── monitor
    └── scoreboard
```

### Hello World UVM

```systemverilog
`include "uvm_macros.svh"
import uvm_pkg::*;

class my_test extends uvm_test;
    `uvm_component_utils(my_test)
    
    function new(string name = "my_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Hello UVM World!", UVM_LOW)
        #100;
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial begin
        run_test("my_test");
    end
endmodule
```

**To run:**
```bash
vcs -sverilog -ntb_opts uvm-1.2 hello_uvm.sv
./simv +UVM_TESTNAME=my_test
```

---

## UVM Architecture

### 1. Transaction (uvm_sequence_item)

The **transaction** is the fundamental unit of communication. It represents a protocol operation.

```systemverilog
class alu_transaction extends uvm_sequence_item;
    rand bit [31:0] a;
    rand bit [31:0] b;
    rand alu_op_t   op;  // ADD, SUB, AND, OR, etc.
    bit [31:0]      result;
    
    // UVM automation macros
    `uvm_object_utils_begin(alu_transaction)
        `uvm_field_int(a, UVM_ALL_ON)
        `uvm_field_int(b, UVM_ALL_ON)
        `uvm_field_enum(alu_op_t, op, UVM_ALL_ON)
        `uvm_field_int(result, UVM_ALL_ON | UVM_NOCOMPARE)
    `uvm_object_utils_end
    
    function new(string name = "alu_transaction");
        super.new(name);
    endfunction
    
    // Constraints
    constraint c_valid_op {
        op inside {ADD, SUB, AND, OR, XOR};
    }
endclass
```

**Key Points:**
- Extends `uvm_sequence_item` (not component!)
- `rand` for randomization
- Field macros for automation (copy, compare, print, pack)
- Constructor takes only name (no parent)

---

### 2. Sequence (uvm_sequence)

**Sequences** generate transactions. Think of them as stimulus generators.

```systemverilog
class alu_base_sequence extends uvm_sequence#(alu_transaction);
    `uvm_object_utils(alu_base_sequence)
    
    function new(string name = "alu_base_sequence");
        super.new(name);
    endfunction
    
    task body();
        alu_transaction tx;
        
        // Generate 10 random transactions
        repeat(10) begin
            tx = alu_transaction::type_id::create("tx");
            start_item(tx);           // Wait for driver ready
            assert(tx.randomize());   // Randomize transaction
            finish_item(tx);          // Send to driver
        end
    endtask
endclass

// Directed sequence example
class alu_add_sequence extends alu_base_sequence;
    `uvm_object_utils(alu_add_sequence)
    
    function new(string name = "alu_add_sequence");
        super.new(name);
    endfunction
    
    task body();
        alu_transaction tx;
        
        repeat(5) begin
            tx = alu_transaction::type_id::create("tx");
            start_item(tx);
            assert(tx.randomize() with {op == ADD;});
            finish_item(tx);
        end
    endtask
endclass
```

**Sequence Flow:**
1. `start_item()`: Request driver, wait if busy
2. `randomize()`: Generate transaction data
3. `finish_item()`: Send to driver, wait for completion

---

### 3. Driver (uvm_driver)

**Driver** converts transactions to pin wiggles.

```systemverilog
class alu_driver extends uvm_driver#(alu_transaction);
    `uvm_component_utils(alu_driver)
    
    virtual alu_if vif;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual alu_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not set")
    endfunction
    
    task run_phase(uvm_phase phase);
        forever begin
            // Get transaction from sequencer
            seq_item_port.get_next_item(req);
            
            // Drive DUT
            drive_transaction(req);
            
            // Signal completion
            seq_item_port.item_done();
        end
    endtask
    
    task drive_transaction(alu_transaction tx);
        @(posedge vif.clk);
        vif.a  <= tx.a;
        vif.b  <= tx.b;
        vif.op <= tx.op;
        vif.valid <= 1'b1;
        
        @(posedge vif.clk);
        vif.valid <= 1'b0;
    endtask
endclass
```

**Key Points:**
- Extends `uvm_driver#(TRANSACTION_TYPE)`
- Gets transactions via `seq_item_port.get_next_item()`
- Drives virtual interface
- `item_done()` signals completion

---

### 4. Monitor (uvm_monitor)

**Monitor** observes DUT and reconstructs transactions.

```systemverilog
class alu_monitor extends uvm_monitor;
    `uvm_component_utils(alu_monitor)
    
    virtual alu_if vif;
    uvm_analysis_port#(alu_transaction) analysis_port;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        analysis_port = new("analysis_port", this);
        if (!uvm_config_db#(virtual alu_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not set")
    endfunction
    
    task run_phase(uvm_phase phase);
        alu_transaction tx;
        forever begin
            // Wait for valid transaction
            @(posedge vif.clk);
            if (vif.valid) begin
                tx = alu_transaction::type_id::create("tx");
                tx.a  = vif.a;
                tx.b  = vif.b;
                tx.op = vif.op;
                
                // Wait for result
                @(posedge vif.clk);
                tx.result = vif.result;
                
                // Broadcast to scoreboard, coverage, etc.
                analysis_port.write(tx);
            end
        end
    endtask
endclass
```

**Key Points:**
- Observes interface (doesn't drive)
- Reconstructs transactions from pin activity
- Broadcasts via `analysis_port` (TLM)
- Multiple subscribers possible (scoreboard, coverage, etc.)

---

### 5. Sequencer (uvm_sequencer)

**Sequencer** routes sequences to driver. Usually just instantiated, not customized.

```systemverilog
class alu_sequencer extends uvm_sequencer#(alu_transaction);
    `uvm_component_utils(alu_sequencer)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass
```

---

### 6. Agent (uvm_agent)

**Agent** encapsulates driver, monitor, sequencer. Can be active or passive.

```systemverilog
class alu_agent extends uvm_agent;
    `uvm_component_utils(alu_agent)
    
    alu_driver    driver;
    alu_monitor   monitor;
    alu_sequencer sequencer;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        monitor = alu_monitor::type_id::create("monitor", this);
        
        if (get_is_active() == UVM_ACTIVE) begin
            driver = alu_driver::type_id::create("driver", this);
            sequencer = alu_sequencer::type_id::create("sequencer", this);
        end
    endfunction
    
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        if (get_is_active() == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction
endclass
```

**Active vs Passive:**
- **Active**: Has driver (generates stimulus)
- **Passive**: Monitor only (observes)

---

### 7. Scoreboard (uvm_scoreboard)

**Scoreboard** checks DUT outputs against expected values.

```systemverilog
class alu_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(alu_scoreboard)
    
    uvm_analysis_imp#(alu_transaction, alu_scoreboard) analysis_export;
    
    int passed, failed;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        analysis_export = new("analysis_export", this);
    endfunction
    
    function void write(alu_transaction tx);
        bit [31:0] expected;
        
        // Calculate expected result
        case (tx.op)
            ADD: expected = tx.a + tx.b;
            SUB: expected = tx.a - tx.b;
            AND: expected = tx.a & tx.b;
            OR:  expected = tx.a | tx.b;
            XOR: expected = tx.a ^ tx.b;
            default: expected = 32'hX;
        endcase
        
        // Compare
        if (tx.result === expected) begin
            passed++;
            `uvm_info("PASS", $sformatf("a=%0d, b=%0d, op=%s, result=%0d", 
                      tx.a, tx.b, tx.op.name(), tx.result), UVM_HIGH)
        end else begin
            failed++;
            `uvm_error("FAIL", $sformatf("a=%0d, b=%0d, op=%s, expected=%0d, got=%0d",
                       tx.a, tx.b, tx.op.name(), expected, tx.result))
        end
    endfunction
    
    function void report_phase(uvm_phase phase);
        `uvm_info("REPORT", $sformatf("Passed: %0d, Failed: %0d", passed, failed), UVM_LOW)
    endfunction
endclass
```

---

### 8. Environment (uvm_env)

**Environment** contains agents and scoreboard. Top-level container.

```systemverilog
class alu_env extends uvm_env;
    `uvm_component_utils(alu_env)
    
    alu_agent      agent;
    alu_scoreboard scoreboard;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        agent = alu_agent::type_id::create("agent", this);
        scoreboard = alu_scoreboard::type_id::create("scoreboard", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        agent.monitor.analysis_port.connect(scoreboard.analysis_export);
    endfunction
endclass
```

---

### 9. Test (uvm_test)

**Test** configures environment and runs sequences.

```systemverilog
class alu_base_test extends uvm_test;
    `uvm_component_utils(alu_base_test)
    
    alu_env env;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = alu_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        alu_base_sequence seq;
        
        phase.raise_objection(this);
        
        seq = alu_base_sequence::type_id::create("seq");
        seq.start(env.agent.sequencer);
        
        phase.drop_objection(this);
    endtask
endclass

// Specific test
class alu_add_test extends alu_base_test;
    `uvm_component_utils(alu_add_test)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        alu_add_sequence seq;
        
        phase.raise_objection(this);
        seq = alu_add_sequence::type_id::create("seq");
        seq.start(env.agent.sequencer);
        phase.drop_objection(this);
    endtask
endclass
```

---

### 10. Top Module

```systemverilog
module tb_top;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Clock and reset
    bit clk;
    bit rst_n;
    
    always #5 clk = ~clk;
    
    initial begin
        rst_n = 0;
        #20 rst_n = 1;
    end
    
    // Interface
    alu_if alu_if_inst(clk, rst_n);
    
    // DUT
    alu dut (
        .clk(alu_if_inst.clk),
        .rst_n(alu_if_inst.rst_n),
        .a(alu_if_inst.a),
        .b(alu_if_inst.b),
        .op(alu_if_inst.op),
        .valid(alu_if_inst.valid),
        .result(alu_if_inst.result)
    );
    
    // Set interface in config_db
    initial begin
        uvm_config_db#(virtual alu_if)::set(null, "*", "vif", alu_if_inst);
        run_test();
    end
    
    // Waveform dump
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, tb_top);
    end
endmodule
```

---

## Key Concepts

### UVM Phases

UVM testbenches execute in phases:

```
Build Phase:     Create component hierarchy
                 ↓
Connect Phase:   Connect ports
                 ↓
End of Elaboration: Final setup
                 ↓
Start of Simulation: Pre-run tasks
                 ↓
Run Phase:       Main simulation (time-consuming)
  ├─ reset_phase
  ├─ configure_phase
  ├─ main_phase
  ├─ shutdown_phase
                 ↓
Extract Phase:   Extract information
                 ↓
Check Phase:     Check results
                 ↓
Report Phase:    Report statistics
                 ↓
Final Phase:     Cleanup
```

**Build Phase:**
```systemverilog
function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = alu_agent::type_id::create("agent", this);
endfunction
```

**Connect Phase:**
```systemverilog
function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    monitor.analysis_port.connect(scoreboard.analysis_export);
endfunction
```

**Run Phase:**
```systemverilog
task run_phase(uvm_phase phase);
    phase.raise_objection(this);  // Keep simulation alive
    // Test logic
    phase.drop_objection(this);   // Allow simulation to end
endtask
```

---

### Factory Pattern

The **factory** enables:
- **Type override**: Replace one component type with another
- **Instance override**: Replace specific instance
- **No code changes**: Override at runtime

**Registration:**
```systemverilog
class my_driver extends uvm_driver#(my_transaction);
    `uvm_component_utils(my_driver)  // Register with factory
    // ...
endclass
```

**Creation:**
```systemverilog
// Instead of: driver = new("driver", this);
driver = my_driver::type_id::create("driver", this);  // Use factory
```

**Override (in test):**
```systemverilog
function void build_phase(uvm_phase phase);
    // Replace all my_driver with my_improved_driver
    my_driver::type_id::set_type_override(my_improved_driver::get_type());
    
    // Or instance-specific:
    set_inst_override_by_type("env.agent.driver", 
                              my_driver::get_type(),
                              my_improved_driver::get_type());
    
    super.build_phase(phase);
endfunction
```

---

### Configuration Database (config_db)

Share configuration across testbench without passing arguments.

**Set (in top module or test):**
```systemverilog
uvm_config_db#(virtual my_if)::set(null, "*", "vif", my_if_inst);
uvm_config_db#(int)::set(null, "env.agent", "num_transactions", 100);
```

**Get (in component):**
```systemverilog
function void build_phase(uvm_phase phase);
    if (!uvm_config_db#(virtual my_if)::get(this, "", "vif", vif))
        `uvm_fatal("NOVIF", "Virtual interface not found")
endfunction
```

**Arguments:**
- **Context**: `null` = global, `this` = current component
- **Instance path**: `"*"` = all, `"env.agent"` = specific
- **Field name**: String identifier
- **Value**: Data to set/get

---

### TLM (Transaction Level Modeling)

TLM provides communication between components.

**Analysis Port (1-to-many broadcast):**
```systemverilog
// Producer
class my_monitor extends uvm_monitor;
    uvm_analysis_port#(my_transaction) analysis_port;
    
    function void build_phase(uvm_phase phase);
        analysis_port = new("analysis_port", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        my_transaction tx;
        // ... collect transaction
        analysis_port.write(tx);  // Broadcast
    endtask
endclass

// Consumer
class my_scoreboard extends uvm_scoreboard;
    uvm_analysis_imp#(my_transaction, my_scoreboard) analysis_export;
    
    function void build_phase(uvm_phase phase);
        analysis_export = new("analysis_export", this);
    endfunction
    
    function void write(my_transaction tx);
        // Process transaction
    endfunction
endclass

// Connect (in environment)
monitor.analysis_port.connect(scoreboard.analysis_export);
```

**TLM FIFO (buffered communication):**
```systemverilog
uvm_tlm_fifo#(my_transaction) fifo;

// Producer
task run_phase(uvm_phase phase);
    fifo.put(tx);  // Blocking put
endtask

// Consumer
task run_phase(uvm_phase phase);
    fifo.get(tx);  // Blocking get
endtask
```

---

## Advanced Topics

### 1. Register Abstraction Layer (RAL)

RAL provides **register-level access** without knowing bus protocol.

**Define registers:**
```systemverilog
class ctrl_reg extends uvm_reg;
    rand uvm_reg_field enable;
    rand uvm_reg_field mode;
    
    `uvm_object_utils(ctrl_reg)
    
    function new(string name = "ctrl_reg");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction
    
    virtual function void build();
        enable = uvm_reg_field::type_id::create("enable");
        enable.configure(this, 1, 0, "RW", 0, 1'b0, 1, 1, 0);
        
        mode = uvm_reg_field::type_id::create("mode");
        mode.configure(this, 2, 1, "RW", 0, 2'b00, 1, 1, 0);
    endfunction
endclass

class my_reg_block extends uvm_reg_block;
    rand ctrl_reg ctrl;
    rand status_reg status;
    
    `uvm_object_utils(my_reg_block)
    
    function new(string name = "my_reg_block");
        super.new(name, UVM_NO_COVERAGE);
    endfunction
    
    virtual function void build();
        default_map = create_map("default_map", 0, 4, UVM_LITTLE_ENDIAN);
        
        ctrl = ctrl_reg::type_id::create("ctrl");
        ctrl.configure(this);
        ctrl.build();
        default_map.add_reg(ctrl, 32'h0, "RW");
        
        status = status_reg::type_id::create("status");
        status.configure(this);
        status.build();
        default_map.add_reg(status, 32'h4, "RO");
    endfunction
endclass
```

**Use in sequence:**
```systemverilog
task body();
    uvm_status_e status;
    
    // Write register
    regmodel.ctrl.enable.set(1'b1);
    regmodel.ctrl.write(status);
    
    // Read register
    regmodel.status.read(status);
    
    // Or simpler:
    regmodel.ctrl.enable.write(status, 1'b1);
    
    // Read-modify-write
    regmodel.ctrl.read(status);
    regmodel.ctrl.mode.set(2'b10);
    regmodel.ctrl.update(status);
endtask
```

---

### 2. Virtual Sequences

Coordinate multiple interfaces:

```systemverilog
class virtual_sequence extends uvm_sequence;
    `uvm_object_utils(virtual_sequence)
    
    my_virtual_sequencer v_sqr;
    
    function new(string name = "virtual_sequence");
        super.new(name);
    endfunction
    
    task body();
        apb_write_seq apb_wr;
        axi_read_seq axi_rd;
        
        fork
            begin
                apb_wr = apb_write_seq::type_id::create("apb_wr");
                apb_wr.start(v_sqr.apb_sqr);
            end
            begin
                axi_rd = axi_read_seq::type_id::create("axi_rd");
                axi_rd.start(v_sqr.axi_sqr);
            end
        join
    endtask
endclass
```

---

### 3. Callbacks

Add functionality without modifying original class:

```systemverilog
// Define callback
class my_driver_callback extends uvm_callback;
    `uvm_object_utils(my_driver_callback)
    
    virtual task pre_drive(my_transaction tx);
        // Default: do nothing
    endtask
endclass

// Driver with callback support
class my_driver extends uvm_driver#(my_transaction);
    `uvm_component_utils(my_driver)
    `uvm_register_cb(my_driver, my_driver_callback)
    
    task drive_transaction(my_transaction tx);
        // Call callbacks
        `uvm_do_callbacks(my_driver, my_driver_callback, pre_drive(tx))
        
        // Drive logic
        // ...
    endtask
endclass

// Specific callback
class error_injection_callback extends my_driver_callback;
    `uvm_object_utils(error_injection_callback)
    
    virtual task pre_drive(my_transaction tx);
        if ($urandom_range(0,99) < 5)  // 5% error rate
            tx.inject_error = 1'b1;
    endtask
endclass

// Register callback (in test)
my_driver_callback cb = error_injection_callback::type_id::create("cb");
uvm_callbacks#(my_driver, my_driver_callback)::add(driver, cb);
```

---

## Constrained Random Verification

### Basic Constraints

```systemverilog
class my_transaction extends uvm_sequence_item;
    rand bit [31:0] addr;
    rand bit [31:0] data;
    rand bit [1:0]  burst_type;
    
    // Address must be 4-byte aligned
    constraint c_addr_aligned {
        addr[1:0] == 2'b00;
    }
    
    // Address in valid range
    constraint c_addr_range {
        addr inside {[32'h0000_0000:32'h0000_FFFF]};
    }
    
    // Data non-zero 90% of time
    constraint c_data_nonzero {
        data dist {0 := 10, [1:32'hFFFF_FFFF] := 90};
    }
    
    // Implication
    constraint c_burst_implies {
        burst_type == 2'b11 -> addr[11:0] == 12'h000;
    }
endclass
```

### Advanced Constraints

```systemverilog
class advanced_transaction extends uvm_sequence_item;
    rand bit [31:0] addr[];
    rand int        num_transfers;
    
    // Dynamic array size
    constraint c_size {
        num_transfers inside {[1:16]};
        addr.size() == num_transfers;
    }
    
    // Array elements
    constraint c_addr_sequence {
        foreach (addr[i]) {
            if (i > 0)
                addr[i] == addr[i-1] + 4;  // Consecutive
        }
    }
    
    // Soft constraint (can be overridden)
    constraint c_default_size {
        soft num_transfers == 8;
    }
endclass

// Inline randomization with override
my_transaction tx = my_transaction::type_id::create("tx");
assert(tx.randomize() with {
    num_transfers == 16;  // Override soft constraint
    addr[0] == 32'h1000;
});
```

### Constraint Modes

```systemverilog
// Disable/enable constraints
tx.c_addr_range.constraint_mode(0);  // Disable
assert(tx.randomize());
tx.c_addr_range.constraint_mode(1);  // Enable

// Disable all randomization of a field
tx.rand_mode(0);  // Disable all
tx.addr.rand_mode(0);  // Just addr
```

---

## Functional Coverage

### Basic Coverage

```systemverilog
class my_coverage extends uvm_subscriber#(my_transaction);
    `uvm_component_utils(my_coverage)
    
    covergroup cg_transaction;
        cp_addr: coverpoint tx.addr {
            bins low    = {[0:1023]};
            bins medium = {[1024:2047]};
            bins high   = {[2048:4095]};
        }
        
        cp_burst: coverpoint tx.burst_type {
            bins single = {0};
            bins incr   = {1};
            bins wrap   = {2};
            illegal_bins illegal = {3};
        }
        
        // Cross coverage
        cross cp_addr, cp_burst;
    endgroup
    
    my_transaction tx;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        cg_transaction = new();
    endfunction
    
    function void write(my_transaction t);
        tx = t;
        cg_transaction.sample();
    endfunction
endclass
```

### Advanced Coverage

```systemverilog
covergroup cg_advanced;
    // Transition bins
    cp_state: coverpoint state {
        bins transitions = (IDLE => ACTIVE => DONE => IDLE);
    }
    
    // Custom bins with range
    cp_data: coverpoint data {
        bins zero     = {0};
        bins small[]  = {[1:10]};      // Create 10 bins
        bins large    = {[100:$]};
        ignore_bins ignore = {32'hDEAD_BEEF};
    }
    
    // Options
    option.per_instance = 1;
    option.at_least = 5;  // Each bin hit 5 times
endgroup
```

---

## Verification Best Practices

### 1. Layered Testbench

Separate concerns:
- **Test Layer**: What to test (sequence selection)
- **Sequence Layer**: Stimulus patterns
- **Driver Layer**: Pin-level driving
- **Monitor Layer**: Protocol observation
- **Checker Layer**: Verification (scoreboard)

### 2. Reusable VIPs

Create reusable verification IPs:
- Parameterizable
- Configurable (master/slave, active/passive)
- Well-documented
- Protocol-compliant
- Include assertions

### 3. Coverage-Driven Verification

```
1. Write functional coverage
2. Run random tests
3. Check coverage (aim for >95%)
4. Write directed tests for holes
5. Repeat until coverage goal met
```

### 4. Assertions

Embed SVA in DUT or interface:
```systemverilog
// In interface or module
property valid_stable;
    @(posedge clk) valid && !ready |=> $stable(data);
endproperty
assert property (valid_stable);
```

### 5. Debug Strategy

1. **Start simple**: Verify basic functionality first
2. **Use reporting**: `uvm_info`, `uvm_error`
3. **Transaction recording**: `uvm_recorder`
4. **Waveforms**: Last resort, look at transactions first
5. **Verbosity levels**: UVM_LOW, UVM_MEDIUM, UVM_HIGH, UVM_DEBUG

---

## Learning Path

### Week 1-2: UVM Basics
- [ ] Hello World UVM
- [ ] Understand phases
- [ ] Create transaction
- [ ] Write simple sequence
- [ ] Basic driver/monitor

### Week 3-4: Build Complete Testbench
- [ ] Agent (driver + monitor + sequencer)
- [ ] Scoreboard
- [ ] Environment
- [ ] Test
- [ ] Run simulation

### Week 5-6: Intermediate Concepts
- [ ] Config DB
- [ ] Factory overrides
- [ ] TLM ports
- [ ] Multiple sequences
- [ ] Coverage

### Week 7-8: Advanced Topics
- [ ] Virtual sequences
- [ ] Callbacks
- [ ] RAL (if register-based DUT)
- [ ] Complex scoreboards

### Week 9+: Master UVM
- [ ] Full chip verification
- [ ] Multiple VIPs
- [ ] Performance optimization
- [ ] Formal + UVM
- [ ] Coverage closure

---

## Common Pitfalls

1. **Forgetting `super.build_phase()`**: Always call parent
2. **Not raising objections**: Simulation ends immediately
3. **Config DB typos**: Field name mismatch = not found
4. **Factory not used**: `new()` instead of `::create()`
5. **TLM port mismatch**: Wrong port/export type
6. **Phase ordering**: Accessing components before built
7. **Memory leaks**: Not using factory for objects
8. **Race conditions**: Monitor vs driver timing

---

## Debugging Tips

### UVM Reporting

```systemverilog
// Different severity levels
`uvm_info(get_type_name(), "Informational message", UVM_LOW)
`uvm_warning(get_type_name(), "Warning message")
`uvm_error(get_type_name(), "Error message")
`uvm_fatal(get_type_name(), "Fatal error - stops simulation")

// Conditional compilation
`ifdef DEBUG
    `uvm_info("DEBUG", $sformatf("addr=%h", addr), UVM_HIGH)
`endif
```

### Command Line Options

```bash
# Set verbosity
+UVM_VERBOSITY=UVM_HIGH

# Specific test
+UVM_TESTNAME=my_specific_test

# Max errors before quit
+UVM_MAX_QUIT_COUNT=10

# Timeout
+UVM_TIMEOUT=100000

# Seed for reproducibility
+ntb_random_seed=12345

# UVM phase debug
+UVM_PHASE_TRACE
```

### Transaction Recording

```systemverilog
// Enable recording
uvm_config_db#(int)::set(null, "*", "recording_detail", UVM_FULL);

// View in waveform viewer with transaction view
```

---

## Complete Example: ALU Testbench

See `complete_examples/simple_alu_uvm/` for full working example with:
- DUT (ALU)
- Interface
- Transaction, sequence, driver, monitor
- Agent, scoreboard, environment
- Multiple tests
- Makefile for simulation

---

## Tools

### Simulators with UVM Support

1. **Synopsys VCS**
   ```bash
   vcs -sverilog -ntb_opts uvm-1.2 files.f
   ./simv +UVM_TESTNAME=my_test
   ```

2. **Cadence Xcelium**
   ```bash
   xrun -uvm files.f
   ```

3. **Mentor Questa**
   ```bash
   vlog -sv files.f
   vsim -c top +UVM_TESTNAME=my_test -do "run -all; quit"
   ```

4. **Aldec Riviera-PRO**
   ```bash
   vlog -sv -work work files.f
   vsim +UVM_TESTNAME=my_test
   ```

---

## References

### Books
- **"The UVM Primer"** - Ray Salemi (START HERE!)
- **"UVM Cookbook"** - Cadence (free online)
- **"A Pragmatic Approach to UVM"** - Salemi
- **"Verification Methodology Manual"** - VMM (pre-UVM)
- **"Writing Testbenches using SystemVerilog"** - Bergeron

### Online Resources
- **Verification Academy** - https://verificationacademy.com (essential!)
- **Accellera UVM** - https://www.accellera.org/downloads/standards/uvm
- **Doulos UVM Tutorials** - https://www.doulos.com/knowhow/sysverilog/uvm/
- **ChipVerify** - https://www.chipverify.com/uvm/

### Standards
- **IEEE 1800.2-2020**: UVM Standard

### Video Courses
- Verification Academy video series
- Udemy UVM courses
- YouTube: "UVM Tutorial" by Verification Guide

---

## Contributing

When adding examples:
1. Follow UVM coding guidelines
2. Use consistent naming (agent_name_*)
3. Include README with runnable example
4. Document configuration options
5. Provide expected output
6. Update this main README

---

**Last Updated**: January 2026
**Maintainer**: System Verilog Workshop
**UVM Version**: 1.2
