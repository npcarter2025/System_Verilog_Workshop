# UVM Components

## Overview
This section covers the three fundamental UVM components that form the backbone of any UVM testbench:
1. **Driver** - Converts transactions to pin wiggles
2. **Monitor** - Converts pin wiggles to transactions  
3. **Sequencer** - Manages transaction flow

## Files
- `driver_example.sv` - Complete driver implementation
- `monitor_example.sv` - Complete monitor with analysis port
- `sequencer_example.sv` - Sequencer and multiple sequence examples

## Component Hierarchy

```
uvm_component (base class for all components)
    │
    ├── uvm_driver
    │
    ├── uvm_monitor
    │
    ├── uvm_sequencer
    │
    ├── uvm_agent
    │
    ├── uvm_env
    │
    └── uvm_test
```

## Driver

### Purpose
- Gets transactions from sequencer via TLM port
- Converts abstract transactions to pin-level stimulus
- Drives signals to DUT via virtual interface

### Key Features
```systemverilog
class my_driver extends uvm_driver#(transaction_type);
    virtual interface_type vif;
    
    // Inherited from uvm_driver:
    // uvm_seq_item_port_base seq_item_port;
    
    task run_phase(uvm_phase phase);
        forever begin
            // Get next item from sequencer
            seq_item_port.get_next_item(req);
            
            // Drive to DUT
            drive_transaction(req);
            
            // Tell sequencer we're done
            seq_item_port.item_done();
        end
    endtask
endclass
```

### Driver API
```systemverilog
// Get next transaction (blocks until available)
seq_item_port.get_next_item(req);

// Try to get transaction (non-blocking)
seq_item_port.try_next_item(req);

// Signal completion
seq_item_port.item_done();

// Signal completion with response
seq_item_port.item_done(rsp);

// Get and signal done in one call
seq_item_port.get(req);

// Peek at next item without removing
seq_item_port.peek(req);

// Put item back
seq_item_port.put(req);
```

## Monitor

### Purpose
- Observes DUT pin activity (passive - never drives!)
- Reconstructs transactions from pin wiggles
- Broadcasts transactions via analysis port

### Key Features
```systemverilog
class my_monitor extends uvm_monitor;
    virtual interface_type vif;
    uvm_analysis_port#(transaction_type) ap;
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        ap = new("ap", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        forever begin
            transaction_type tr;
            
            // Observe and collect
            tr = collect_transaction();
            
            // Broadcast to subscribers
            ap.write(tr);
        end
    endtask
endclass
```

### Monitor Best Practices
1. **Never drive signals** - Monitor is passive
2. **Use monitor clocking block** - All signals as inputs
3. **Sample at handshake** - When valid && ready
4. **Save immediately** - Signals change every cycle
5. **Broadcast via analysis port** - Not seq_item_port!

## Sequencer

### Purpose
- Acts as transaction mailbox between sequences and driver
- Arbitrates between multiple sequences
- Provides TLM interface for communication

### Basic Sequencer (typedef)
```systemverilog
// For most cases, a typedef is sufficient
typedef uvm_sequencer#(transaction_type) my_sequencer;
```

### Custom Sequencer (extended)
```systemverilog
class custom_sequencer extends uvm_sequencer#(transaction_type);
    `uvm_component_utils(custom_sequencer)
    
    // Add custom fields
    int max_outstanding = 8;
    
    // Override methods for custom behavior
    task get_next_item(output REQ t);
        // Custom logic here
        super.get_next_item(t);
    endtask
endclass
```

## Connecting Components

### In Agent's connect_phase:
```systemverilog
function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    // Connect driver to sequencer
    driver.seq_item_port.connect(sequencer.seq_item_export);
    
    // Connect monitor to subscriber (if any)
    monitor.ap.connect(subscriber.analysis_export);
endfunction
```

## TLM Communication

### Ports vs Exports
- **Port**: Initiates transaction (driver has seq_item_port)
- **Export**: Provides transaction (sequencer has seq_item_export)
- **Analysis Port**: Broadcasts (monitor has analysis_port)
- **Analysis Export**: Receives (subscriber has analysis_export)

```
  Driver                    Sequencer
┌──────────┐              ┌───────────┐
│seq_item_ │   connect    │seq_item_  │
│  port    │─────────────>│  export   │
└──────────┘              └───────────┘

  Monitor                   Subscriber
┌──────────┐              ┌───────────┐
│analysis_ │   connect    │analysis_  │
│  port    │─────────────>│  export   │
└──────────┘              └───────────┘
```

## Complete Agent Example

```systemverilog
class my_agent extends uvm_agent;
    `uvm_component_utils(my_agent)
    
    my_driver driver;
    my_monitor monitor;
    my_sequencer sequencer;
    
    uvm_active_passive_enum is_active = UVM_ACTIVE;
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        monitor = my_monitor::type_id::create("monitor", this);
        
        if (is_active == UVM_ACTIVE) begin
            driver = my_driver::type_id::create("driver", this);
            sequencer = my_sequencer::type_id::create("sequencer", this);
        end
    endfunction
    
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        if (is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction
endclass
```

## Running the Examples

### Driver Example:
```bash
vlog -sv driver_example.sv
vsim -c top -do "run -all; quit"
```

### Monitor Example:
```bash
vlog -sv monitor_example.sv
vsim -c top -do "run -all; quit"
```

### Sequencer Example:
```bash
vlog -sv sequencer_example.sv
vsim -c top -do "run -all; quit"
```

## Exercises

### Exercise 1: Add Response
Modify the driver to send responses back to the sequence:
```systemverilog
seq_item_port.item_done(rsp);
```

### Exercise 2: Monitor Statistics
Add counters in the monitor to track:
- Total transactions
- Transactions per second
- Average data value

### Exercise 3: Custom Arbitration
Extend the sequencer to implement:
- Priority-based arbitration
- Round-robin arbitration
- Weighted arbitration

### Exercise 4: Bidirectional Driver
Create a driver that handles both:
- Requests (to DUT)
- Responses (from DUT)

## Common Pitfalls

### ❌ Driver using wrong port
```systemverilog
// WRONG - Driver should use seq_item_port, not analysis_port
uvm_analysis_port#(my_tr) ap;
```

### ❌ Monitor driving signals
```systemverilog
// WRONG - Monitor should only observe!
vif.data <= 32'h0;  // Never drive in monitor!
```

### ❌ Forgetting item_done()
```systemverilog
seq_item_port.get_next_item(req);
drive_transaction(req);
// MISSING: seq_item_port.item_done();
// Result: Sequencer hangs!
```

### ❌ Wrong connection direction
```systemverilog
// WRONG
sequencer.seq_item_export.connect(driver.seq_item_port);

// CORRECT
driver.seq_item_port.connect(sequencer.seq_item_export);
```

## Next Steps
- **03_transactions**: Learn about transaction objects and field macros
- **04_sequences**: Master sequence creation and patterns
- **05_agent**: Build complete agents with configuration

## References
- [UVM 1.2 Class Reference](https://www.accellera.org/images/downloads/standards/uvm/UVM_Class_Reference_Manual_1.2.pdf)
- [UVM Cookbook - TLM](https://verificationacademy.com/cookbook/tlm)
