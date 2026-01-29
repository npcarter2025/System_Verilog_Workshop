# 08 - Low Power Design Techniques

This directory contains SystemVerilog implementations and examples of various low-power design techniques used in modern ASIC and FPGA design. These techniques are essential for power-conscious designs in mobile, IoT, and high-performance computing applications.

## Table of Contents

- [Overview](#overview)
- [Directory Structure](#directory-structure)
- [Topics Covered](#topics-covered)
- [Key Concepts](#key-concepts)
- [Prerequisites](#prerequisites)
- [Tools and Methodologies](#tools-and-methodologies)
- [Learning Path](#learning-path)
- [References](#references)

---

## Overview

Low-power design is critical in modern digital systems where battery life, thermal management, and energy efficiency are paramount. This section covers both RTL-level techniques and design methodologies for reducing power consumption in digital circuits.

**Power consumption** in CMOS circuits consists of:
- **Dynamic Power**: P_dynamic = α × C × V² × f (switching activity)
- **Static Power**: P_static = V × I_leakage (leakage current)
- **Short-circuit Power**: During transitions

---

## Directory Structure

```
08_low_power/
├── README.md                        # This file
├── clock_gating/
│   ├── integrated_clock_gating/
│   │   ├── icg_cell.sv              # Latch-based clock gate
│   │   ├── icg_safe.sv              # Glitch-free implementation
│   │   ├── icg_tb.sv                # Testbench
│   │   └── README.md
│   ├── rtl_clock_gating/
│   │   ├── auto_gated_reg.sv        # Register with enable gating
│   │   ├── conditional_gating.sv    # Gate based on logic conditions
│   │   ├── pipeline_gating.sv       # Gate pipeline stages
│   │   └── README.md
│   └── clock_gating_assertions.sv   # SVA to verify no glitches
├── power_domains/
│   ├── isolation_cells/
│   │   ├── iso_cell_high.sv         # Clamp to high when off
│   │   ├── iso_cell_low.sv          # Clamp to low when off
│   │   ├── iso_cell_latch.sv        # Latch last value
│   │   └── README.md
│   ├── level_shifters/
│   │   ├── level_shifter_up.sv      # Low to high voltage
│   │   ├── level_shifter_down.sv    # High to low voltage
│   │   └── README.md
│   └── power_switches/
│       ├── header_switch.sv         # PMOS power switch
│       ├── footer_switch.sv         # NMOS ground switch
│       └── README.md
├── retention/
│   ├── retention_register.sv        # Retains value in sleep mode
│   ├── retention_fifo.sv            # FIFO with retention
│   ├── save_restore_fsm.sv          # State save/restore logic
│   └── README.md
├── dvfs/                            # Dynamic Voltage/Frequency Scaling
│   ├── freq_divider_dynamic.sv      # Runtime frequency adjustment
│   ├── voltage_monitor.sv           # Simple voltage detector
│   ├── performance_counter.sv       # Track activity for DVFS
│   └── README.md
├── power_aware_design/
│   ├── operand_isolation.sv         # Prevent toggling unused logic
│   ├── memory_power_down.sv         # RAM sleep modes
│   ├── multi_vt_example.sv          # High-Vt and Low-Vt usage notes
│   ├── gated_compute_unit.sv        # Power gate entire block
│   └── README.md
├── upf_examples/                    # Unified Power Format
│   ├── simple_power_domain.upf      # Basic UPF commands
│   ├── multi_domain.upf             # Multiple power domains
│   ├── isolation_strategy.upf       # Isolation cells specification
│   ├── retention_strategy.upf       # Retention specification
│   └── README.md
└── verification/
    ├── power_aware_tb.sv            # Testbench for power modes
    ├── power_state_monitor.sv       # Check legal power states
    ├── retention_checker.sv         # Verify data retention
    └── README.md
```

---

## Topics Covered

### 1. Clock Gating

Clock gating is one of the most effective techniques for reducing dynamic power by disabling the clock to inactive circuit blocks.

#### **Integrated Clock Gating (ICG)**
- Latch-based clock gating cells
- Glitch-free clock gating
- Test mode bypass
- AND vs OR gate implementations

**Example: Basic ICG Cell**
```systemverilog
// Glitch-free clock gating cell
module icg_cell (
    input  logic clk,
    input  logic en,       // Enable signal
    input  logic test_en,  // Test mode bypass
    output logic gclk      // Gated clock
);
    logic en_latched;
    
    // Latch on negative edge to avoid glitches
    always_latch begin
        if (!clk)
            en_latched <= en | test_en;
    end
    
    assign gclk = clk & en_latched;
endmodule
```

**Key Points:**
- Latch opens on low phase of clock (transparent when clk=0)
- Enable captured when stable
- Prevents glitches on clock output
- Test enable for scan testing

#### **RTL Clock Gating**
- Automatic clock gating by synthesis tools
- Manual insertion of enable conditions
- Pipeline stage gating
- Conditional computation gating

---

### 2. Power Domains

Power domains allow different parts of a chip to operate at different voltages or be powered off independently.

#### **Isolation Cells**
Prevent unknown values (X) from propagating from powered-off domains to powered-on domains.

**Example: Isolation Cell**
```systemverilog
// Clamps output to 0 when domain is powered off
module iso_cell_low (
    input  logic data_in,
    input  logic iso_en,   // 1 = isolate (power off)
    output logic data_out
);
    assign data_out = iso_en ? 1'b0 : data_in;
endmodule
```

**Types:**
- **iso_low**: Clamps to 0
- **iso_high**: Clamps to 1
- **iso_latch**: Latches last valid value

#### **Level Shifters**
Convert signals between different voltage domains.

**Use Cases:**
- Core running at 0.8V communicating with I/O at 1.8V
- Low-power domain to always-on domain
- Bidirectional level shifting

#### **Power Switches**
Control power supply to entire domains.

**Types:**
- **Header switch**: PMOS between VDD and virtual VDD
- **Footer switch**: NMOS between VSS and virtual VSS
- Can be distributed across design

---

### 3. State Retention

Retention techniques preserve critical state when blocks are powered down.

**Example: Retention Register**
```systemverilog
// Register that retains value during power down
module retention_register #(parameter WIDTH = 32) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             save,      // Save to retention
    input  logic             restore,   // Restore from retention
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);
    logic [WIDTH-1:0] retention_storage;  // Retention flops (always powered)
    logic [WIDTH-1:0] working_storage;     // Normal flops (can power down)
    
    // Save current value to retention storage
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            retention_storage <= '0;
        else if (save)
            retention_storage <= working_storage;
    end
    
    // Normal operation or restore
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            working_storage <= '0;
        else if (restore)
            working_storage <= retention_storage;
        else
            working_storage <= data_in;
    end
    
    assign data_out = working_storage;
endmodule
```

**Key Concepts:**
- Retention flops in always-on domain
- Save/restore protocol
- Balloon/shadow registers
- Application: CPU state, control registers

---

### 4. Dynamic Voltage and Frequency Scaling (DVFS)

Adjust voltage and frequency based on performance requirements.

**Techniques:**
- Runtime frequency adjustment
- Voltage scaling with frequency
- Performance monitoring
- Workload prediction

**Benefits:**
- Significant power savings during low activity
- Thermal management
- Extended battery life

**Challenges:**
- Voltage/frequency transition time
- PLL lock time
- System synchronization

---

### 5. Power-Aware Design Techniques

#### **Operand Isolation**
Prevent unnecessary toggling in unused computational units.

```systemverilog
// Example: Isolate multiplier inputs when not in use
module gated_multiplier (
    input  logic [31:0] a, b,
    input  logic        valid,
    output logic [63:0] product
);
    logic [31:0] a_gated, b_gated;
    
    // Isolate inputs when not valid
    assign a_gated = valid ? a : 32'h0;
    assign b_gated = valid ? b : 32'h0;
    
    assign product = a_gated * b_gated;
endmodule
```

#### **Memory Power Management**
- Shut down unused memory banks
- Reduce bitline swing
- Light sleep vs deep sleep modes
- Retention modes for memories

#### **Multi-Threshold Voltage (Multi-Vt)**
- **Low-Vt**: Fast, high leakage (critical paths)
- **Standard-Vt**: Balance (most logic)
- **High-Vt**: Slow, low leakage (non-critical paths)

---

### 6. Unified Power Format (UPF)

Industry-standard format for specifying power intent.

**Example: Simple UPF**
```tcl
# Define power domains
create_power_domain PD_TOP
create_power_domain PD_CORE -elements {core_inst}

# Power supplies
create_supply_net VDD -domain PD_TOP
create_supply_net VDD_CORE -domain PD_CORE

# Power states
create_pst my_pst -supplies {VDD VDD_CORE}
add_pst_state ON  -pst my_pst -state {VDD 1.2 VDD_CORE 1.0}
add_pst_state OFF -pst my_pst -state {VDD 1.2 VDD_CORE 0.0}

# Isolation strategy
set_isolation iso_core -domain PD_CORE \
              -isolation_power_net VDD \
              -clamp_value 0
```

**UPF Concepts:**
- Power domains definition
- Supply networks
- Power states (PSTs)
- Isolation strategies
- Level shifter strategies
- Retention strategies

---

## Key Concepts

### Power Consumption Breakdown

| Component | Typical % | Mitigation |
|-----------|-----------|------------|
| **Dynamic (switching)** | 50-70% | Clock gating, operand isolation |
| **Static (leakage)** | 30-50% | Power gating, multi-Vt |
| **Short-circuit** | <5% | Proper sizing, low slew |

### Design Flow

1. **Architecture**: Power domain planning
2. **RTL**: Clock gating, FSM optimization
3. **Synthesis**: Multi-Vt cell selection
4. **Place & Route**: Power grid, special cells
5. **Verification**: Power-aware simulation
6. **Sign-off**: Power analysis, IR drop

---

## Prerequisites

- Understanding of digital design fundamentals
- Knowledge of CMOS circuits and power dissipation
- Familiarity with SystemVerilog
- Basic understanding of clock distribution

---

## Tools and Methodologies

### Simulation Tools
- **ModelSim/Questa**: Functional simulation
- **VCS**: Power-aware simulation with SAIF
- **Xcelium**: UPF-aware simulation

### Synthesis Tools
- **Synopsys Design Compiler**: Clock gating, multi-Vt
- **Cadence Genus**: Power optimization

### Power Analysis
- **PrimeTime PX**: Static power analysis
- **Voltus**: Dynamic IR drop
- **Joules**: RTL power estimation

### UPF Tools
- **Synopsys**: CPF (Common Power Format)
- **Cadence**: UPF native support
- **IEEE 1801**: UPF standard

---

## Learning Path

### Beginner
1. Start with **clock gating** examples
2. Understand **ICG cells** and their necessity
3. Learn **RTL coding** for low power
4. Study **power domains** concept

### Intermediate
5. Implement **isolation** and **level shifters**
6. Work with **retention** techniques
7. Create **UPF** for simple designs
8. Practice **power-aware verification**

### Advanced
9. Multi-domain **complex SoC** power architecture
10. **DVFS** implementation
11. **Advanced UPF** with CPF
12. **Static power analysis** methodology

---

## Design Guidelines

### Clock Gating Best Practices
✅ **DO:**
- Use library ICG cells (vendor-provided)
- Gate at module or block level
- Add test enable for scan
- Gate early in clock tree

❌ **DON'T:**
- Create custom clock gates (use vendor cells)
- Gate individual registers (too fine-grained)
- Forget glitch-free guarantee
- Skip formal verification of gating logic

### Power Domain Best Practices
✅ **DO:**
- Plan power domains early (architecture phase)
- Use isolation on all domain crossings
- Verify power sequences carefully
- Document power states clearly

❌ **DON'T:**
- Mix power domain logic
- Forget isolation cells
- Skip retention planning
- Ignore voltage-aware timing

### General Low-Power RTL Guidelines
✅ **DO:**
- Use enable signals on registers
- Minimize glitching in combinational logic
- One-hot encoding for low-activity FSMs
- Gray codes for CDC and counters

❌ **DON'T:**
- Excessive clock domain crossings
- Ripple counters (high toggle rate)
- Unguarded arithmetic (isolate operands)
- Ignore synthesis pragmas

---

## Verification Considerations

### Functional Verification
- Power state transitions
- Isolation effectiveness
- Retention save/restore
- Level shifter operation

### Assertions
```systemverilog
// Example: Verify isolation
property iso_check;
    @(posedge clk) disable iff (!rst_n)
    power_down |-> ##1 (output_signal == ISO_VALUE);
endproperty
assert property (iso_check);

// Example: No glitches on gated clock
property no_glitch;
    @(posedge clk) disable iff (!rst_n)
    !en |=> $stable(gclk);
endproperty
assert property (no_glitch);
```

### Power Analysis
- Power-aware simulation (UPF + VCD/SAIF)
- Toggle rate analysis
- Static power estimation
- IR drop analysis

---

## Common Pitfalls

1. **Clock Gating Glitches**: Use proper ICG cells
2. **Missing Isolation**: Leads to X propagation
3. **Retention Data Loss**: Verify save timing
4. **Level Shifter Delay**: Account in timing
5. **Power Switch Inrush**: Gradual turn-on
6. **UPF Inconsistency**: RTL and UPF must match

---

## Real-World Applications

### Mobile Processors
- Aggressive clock gating (95%+ gates off in idle)
- Multiple power domains (CPU, GPU, modem)
- DVFS for performance/power balance

### IoT Devices
- Deep sleep modes
- Retention for quick wake-up
- Ultra-low leakage (high-Vt)

### Data Centers
- Power gating of idle servers
- Dynamic frequency scaling
- Thermal throttling

---

## References

### Standards
- **IEEE 1801**: Unified Power Format (UPF)
- **IEC 61606-4**: CPF (Common Power Format)

### Books
- "Low Power Methodology Manual" - Synopsys
- "Power-Aware Design Methodologies" - Macii et al.
- "CMOS VLSI Design" - Weste & Harris (Power chapter)

### Papers
- "Clock Gating and Its Application to Low Power Design" - Benini et al.
- "Dynamic Voltage Scaling: The New Paradigm" - Burd & Brodersen

### Online Resources
- Synopsys Low Power Tutorials
- ARM Power Management Documentation
- Cadence UPF User Guide

### Industry Guidelines
- ARM AMBA Power Specifications
- TSMC Low Power Design Guidelines
- Intel Power Optimization Guides

---

## Contributing

When adding new examples to this directory:
1. Include comprehensive comments
2. Add testbench demonstrating functionality
3. Document synthesis results (if applicable)
4. Include assertions for verification
5. Update this README with description

---

## Notes

- Examples are simplified for learning purposes
- Real implementations require vendor-specific cells
- Always verify power intent with formal tools
- Power numbers are process and design dependent

---

**Last Updated**: January 2026
**Maintainer**: System Verilog Workshop
