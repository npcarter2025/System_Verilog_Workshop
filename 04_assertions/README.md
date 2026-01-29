# 04 - SystemVerilog Assertions (SVA)

This directory covers SystemVerilog Assertions (SVA), a powerful declarative language for specifying design intent and creating self-checking testbenches. SVA is essential for both simulation and formal verification.

## Table of Contents

- [Overview](#overview)
- [Directory Structure](#directory-structure)
- [Assertion Types](#assertion-types)
- [SVA Syntax](#sva-syntax)
- [Common Patterns](#common-patterns)
- [Learning Path](#learning-path)
- [References](#references)

---

## Overview

**SystemVerilog Assertions (SVA)** allow you to specify:
- **Design intent**: What should happen
- **Protocol rules**: Valid signal relationships
- **Temporal behavior**: Sequences across time
- **Coverage goals**: What to verify

**Benefits:**
- Self-documenting code
- Early bug detection
- Formal verification enablement
- Functional coverage

---

## Directory Structure

```
04_assertions/
├── README.md
├── immediate/
│   ├── basic_immediate.sv
│   ├── error_checking.sv
│   └── README.md
├── concurrent/
│   ├── property_basics.sv
│   ├── sequence_basics.sv
│   ├── implication.sv
│   ├── repetition.sv
│   └── README.md
├── operators/
│   ├── temporal_operators.sv
│   ├── sequence_operators.sv
│   ├── property_operators.sv
│   └── README.md
├── protocol_assertions/
│   ├── handshake_checks.sv
│   ├── valid_ready.sv
│   ├── axi_assertions.sv
│   ├── apb_assertions.sv
│   └── README.md
├── functional_properties/
│   ├── fifo_properties.sv
│   ├── arbiter_properties.sv
│   ├── memory_properties.sv
│   └── README.md
└── coverage_assertions/
    ├── cover_properties.sv
    ├── assertion_coverage.sv
    └── README.md
```

---

## Assertion Types

### 1. Immediate Assertions

Execute like procedural statements, check conditions **now**.

```systemverilog
always @(posedge clk) begin
    // Simple check
    assert (count >= 0) else $error("Count negative!");
    
    // With custom message
    assert (wr_en || rd_en) 
        else $error("At least one operation required");
    
    // Non-fatal warning
    assert (data_valid) else $warning("Data not valid");
    
    // Assume (for formal)
    assume (rst_n == 1'b1) else $fatal("Reset asserted");
end
```

**Use cases:**
- Sanity checks in procedural code
- State machine checks
- Simple value verification

---

### 2. Concurrent Assertions

Evaluate across clock cycles, describe **temporal behavior**.

```systemverilog
// Property definition
property req_followed_by_ack;
    @(posedge clk) disable iff (!rst_n)
    req |-> ##[1:3] ack;  // ack within 1-3 cycles
endproperty

// Assert the property
assert property (req_followed_by_ack) 
    else $error("Ack not received in time");

// Cover to verify property is exercised
cover property (req_followed_by_ack);
```

---

## SVA Syntax

### Basic Structure

```systemverilog
// Sequence: Pattern over time
sequence seq_name;
    signal1 ##1 signal2 ##1 signal3;
endsequence

// Property: Assertion statement
property prop_name;
    @(posedge clk) disable iff (!rst_n)
    antecedent |-> consequent;
endproperty

// Assert, assume, or cover
assert property (prop_name);
assume property (prop_name);  // For formal
cover property (prop_name);   // For coverage
```

---

### Temporal Operators

| Operator | Meaning | Example |
|----------|---------|---------|
| `##N` | Delay by N cycles | `a ##2 b` (b occurs 2 cycles after a) |
| `##[m:n]` | Delay range | `a ##[1:5] b` (b within 1-5 cycles) |
| `##[m:$]` | Unbounded delay | `a ##[1:$] b` (b eventually) |
| `[*N]` | Repetition | `a[*3]` (a for 3 consecutive cycles) |
| `[*m:n]` | Repetition range | `a[*2:5]` (a for 2 to 5 cycles) |
| `[->N]` | Goto repetition | `a[->3]` (a occurs 3 times, not necessarily consecutive) |
| `[=N]` | Non-consecutive repetition | `a[=3]` (3rd occurrence of a) |

---

### Implication Operators

| Operator | Type | Meaning |
|----------|------|---------|
| `|->` | Overlapping | If antecedent true, consequent must be true **same cycle** |
| `|=>` | Non-overlapping | If antecedent true, consequent must be true **next cycle** |

```systemverilog
// Overlapping: req and ack same cycle
property overlap;
    @(posedge clk) req |-> ack;
endproperty

// Non-overlapping: req now, ack next cycle
property non_overlap;
    @(posedge clk) req |=> ack;
endproperty
```

---

### Sequence Operators

```systemverilog
// Concatenation
sequence seq1;
    a ##1 b ##1 c;
endsequence

// OR
sequence seq_or;
    (a ##1 b) or (c ##1 d);
endsequence

// AND (both must match starting from same time)
sequence seq_and;
    (a ##1 b) and (c ##2 d);
endsequence

// Intersection (same end time)
sequence seq_intersect;
    (a ##[1:5] b) intersect (c ##3 d);
endsequence

// Within
sequence seq_within;
    a ##[1:$] b within c ##[1:$] d;
endsequence

// Throughout (condition holds for entire sequence)
sequence seq_throughout;
    enable throughout (a ##1 b ##1 c);
endsequence
```

---

## Common Patterns

### 1. Handshake Protocol

```systemverilog
// Valid-ready handshake
property valid_stable;
    @(posedge clk) disable iff (!rst_n)
    valid && !ready |=> valid;  // Valid stays high until ready
endproperty
assert property (valid_stable) else $error("Valid dropped");

property data_stable;
    @(posedge clk) disable iff (!rst_n)
    valid && !ready |=> $stable(data);  // Data stable while waiting
endproperty
assert property (data_stable) else $error("Data changed");

// Eventually ready (bounded)
property eventual_ready;
    @(posedge clk) disable iff (!rst_n)
    valid |-> ##[1:10] ready;  // Ready within 10 cycles
endproperty
assert property (eventual_ready) else $error("Timeout");
```

---

### 2. FIFO Checks

```systemverilog
// Never overflow
property no_overflow;
    @(posedge clk) disable iff (!rst_n)
    full |-> !push;
endproperty
assert property (no_overflow) else $error("FIFO overflow");

// Never underflow
property no_underflow;
    @(posedge clk) disable iff (!rst_n)
    empty |-> !pop;
endproperty
assert property (no_underflow) else $error("FIFO underflow");

// Mutual exclusion of full and empty
property full_empty_mutex;
    @(posedge clk) disable iff (!rst_n)
    !(full && empty);
endproperty
assert property (full_empty_mutex);
```

---

### 3. Arbiter Fairness

```systemverilog
// Request eventually granted (with timeout)
property req_granted;
    @(posedge clk) disable iff (!rst_n)
    req[i] |-> ##[1:MAX_WAIT] grant[i];
endproperty
assert property (req_granted) else $error("Starvation");

// One-hot grant
property onehot_grant;
    @(posedge clk) disable iff (!rst_n)
    $onehot0(grant);  // At most one hot
endproperty
assert property (onehot_grant);

// Grant only if requested
property grant_implies_req;
    @(posedge clk) disable iff (!rst_n)
    grant[i] |-> req[i];
endproperty
assert property (grant_implies_req);
```

---

### 4. State Machine

```systemverilog
// Legal transitions
property legal_transitions;
    @(posedge clk) disable iff (!rst_n)
    (state == IDLE)   |=> (state inside {IDLE, ACTIVE}) ##0
    (state == ACTIVE) |=> (state inside {ACTIVE, DONE}) ##0
    (state == DONE)   |=> (state == IDLE);
endproperty
assert property (legal_transitions) else $error("Illegal state transition");

// Reset brings to IDLE
property reset_to_idle;
    @(posedge clk)
    !rst_n |=> state == IDLE;
endproperty
assert property (reset_to_idle);
```

---

### 5. AXI Protocol

```systemverilog
// AWVALID stable until AWREADY
property aw_valid_stable;
    @(posedge aclk) disable iff (!aresetn)
    awvalid && !awready |=> awvalid;
endproperty
assert property (aw_valid_stable) else $error("AWVALID dropped");

// AWADDR stable while AWVALID && !AWREADY
property aw_addr_stable;
    @(posedge aclk) disable iff (!aresetn)
    awvalid && !awready |=> $stable(awaddr);
endproperty
assert property (aw_addr_stable) else $error("AWADDR changed");

// Write response after write data
property b_after_w;
    @(posedge aclk) disable iff (!aresetn)
    (wvalid && wready && wlast) |-> ##[1:10] (bvalid && bready);
endproperty
assert property (b_after_w);
```

---

### 6. Clock Domain Crossing

```systemverilog
// Data stable during handshake
property data_stable_cdc;
    @(posedge clk_src) disable iff (!rst_n)
    req && !ack |=> $stable(data);
endproperty
assert property (data_stable_cdc);

// Only one bit changes (gray code)
property gray_code_check;
    @(posedge clk)
    $countones(gray_code ^ $past(gray_code)) <= 1;
endproperty
assert property (gray_code_check);
```

---

## System Functions

Useful functions in assertions:

| Function | Description | Example |
|----------|-------------|---------|
| `$past(signal, n)` | Value n cycles ago | `$past(valid, 1)` |
| `$rose(signal)` | Rising edge | `$rose(interrupt)` |
| `$fell(signal)` | Falling edge | `$fell(enable)` |
| `$stable(signal)` | Value unchanged | `$stable(data)` |
| `$onehot(vector)` | Exactly one bit set | `$onehot(grant)` |
| `$onehot0(vector)` | At most one bit set | `$onehot0(grant)` |
| `$countones(vector)` | Number of 1's | `$countones(mask)` |
| `$isunknown(signal)` | Has X or Z | `!$isunknown(data)` |

---

## Assert, Assume, Cover

```systemverilog
// ASSERT: Check design behavior
assert property (prop) else $error("Assertion failed");

// ASSUME: Constrain inputs (for formal)
assume property (@(posedge clk) disable iff (!rst_n)
    req |-> ##[1:5] ack);  // Assume environment provides ack

// COVER: Verify property is exercised
cover property (prop);  // Track if property triggered
```

---

## Severity Levels

```systemverilog
// Error (default) - count as failure
assert property (prop) else $error("Error message");

// Warning - report but don't fail
assert property (prop) else $warning("Warning message");

// Info - just information
assert property (prop) else $info("Info message");

// Fatal - stop simulation
assert property (prop) else $fatal("Fatal error");
```

---

## Disable Condition

Most properties should have reset disable:

```systemverilog
property my_prop;
    @(posedge clk) disable iff (!rst_n)  // Disable during reset
    antecedent |-> consequent;
endproperty
```

---

## Binding Assertions

Three ways to add assertions:

### 1. In Module
```systemverilog
module fifo(...);
    // ... RTL code
    
    // Embedded assertions
    assert property (@(posedge clk) disable iff (!rst_n)
        full |-> !push);
endmodule
```

### 2. In Interface
```systemverilog
interface axi_if(input logic clk);
    // ... signals
    
    // Protocol assertions
    property valid_stable;
        @(posedge clk) valid && !ready |=> valid;
    endproperty
    assert property (valid_stable);
endinterface
```

### 3. Bind Statement (Non-intrusive)
```systemverilog
// Separate file: fifo_assertions.sv
module fifo_assertions(
    input logic clk, rst_n,
    input logic push, pop,
    input logic full, empty
);
    property no_overflow;
        @(posedge clk) disable iff (!rst_n)
        full |-> !push;
    endproperty
    assert property (no_overflow);
endmodule

// In testbench
bind fifo fifo_assertions checker(.*);
```

---

## Learning Path

### Week 1: Basics
- Immediate assertions
- Simple concurrent properties
- `##`, `|->`, `|=>`

### Week 2: Sequences
- Sequence definitions
- Repetition operators `[*]`, `[->]`
- Sequence composition

### Week 3: Properties
- Complex properties
- System functions (`$past`, `$stable`)
- Implication variants

### Week 4: Protocols
- Handshake assertions
- Valid-ready protocol
- FIFO properties

### Week 5: Advanced
- Recursive properties
- Local variables
- Formal verification intent

---

## Best Practices

### DO:
✅ Add `disable iff` for reset conditions  
✅ Use meaningful assertion names  
✅ Add error messages for debugging  
✅ Cover properties to ensure they trigger  
✅ Keep properties simple and focused  
✅ Document complex temporal logic

### DON'T:
❌ Forget to check assertion return values  
❌ Over-complicate properties  
❌ Use assertions for functional logic  
❌ Ignore warnings about vacuous passes  
❌ Skip coverage of corner cases

---

## Common Pitfalls

1. **Vacuous pass**: Antecedent never true
   ```systemverilog
   // Bad: If req never happens, property vacuously passes
   property bad_prop;
       req |-> ack;
   endproperty
   
   // Fix: Add cover to verify req happens
   cover property (@(posedge clk) req);
   ```

2. **Clock edge mismatch**: Different clocks in sequence
   ```systemverilog
   // Bad: Mixed clock edges
   property bad_clock;
       @(posedge clk) a ##1 @(negedge clk) b;  // Don't do this!
   endproperty
   ```

3. **Unbounded liveness**: Can't prove in finite time
   ```systemverilog
   // Hard to verify: "eventually" without bound
   property unbounded;
       req |-> ##[1:$] ack;  // When does it fail?
   endproperty
   
   // Better: Bounded
   property bounded;
       req |-> ##[1:100] ack;  // Specific timeout
   endproperty
   ```

---

## Simulation vs Formal

| Aspect | Simulation | Formal Verification |
|--------|-----------|-------------------|
| **Assert** | Check during simulation | Prove mathematically |
| **Assume** | Ignored | Constrain inputs |
| **Cover** | Track hits | Prove reachable |
| **Scope** | Specific tests | All possible inputs |

---

## Example: Complete FIFO Assertions

```systemverilog
module fifo_assertions #(parameter DEPTH = 16) (
    input logic clk,
    input logic rst_n,
    input logic push,
    input logic pop,
    input logic full,
    input logic empty,
    input logic [$clog2(DEPTH):0] count
);

    // Safety: No overflow
    property no_overflow;
        @(posedge clk) disable iff (!rst_n)
        full |-> !push;
    endproperty
    a_no_overflow: assert property (no_overflow)
        else $error("FIFO overflow detected");
    
    // Safety: No underflow
    property no_underflow;
        @(posedge clk) disable iff (!rst_n)
        empty |-> !pop;
    endproperty
    a_no_underflow: assert property (no_underflow)
        else $error("FIFO underflow detected");
    
    // Consistency: Count matches flags
    property count_empty;
        @(posedge clk) disable iff (!rst_n)
        (count == 0) == empty;
    endproperty
    a_count_empty: assert property (count_empty);
    
    property count_full;
        @(posedge clk) disable iff (!rst_n)
        (count == DEPTH) == full;
    endproperty
    a_count_full: assert property (count_full);
    
    // Count increment on push (when not popping)
    property count_incr;
        @(posedge clk) disable iff (!rst_n)
        push && !pop && !full |=> count == $past(count) + 1;
    endproperty
    a_count_incr: assert property (count_incr);
    
    // Coverage: Reach full
    c_full: cover property (@(posedge clk) full);
    
    // Coverage: Back-to-back operations
    c_push_pop: cover property (@(posedge clk) 
        push && !full ##1 pop && !empty);

endmodule
```

---

## Tools Support

- **Simulation**: All major simulators (VCS, Xcelium, Questa)
- **Formal**: Cadence JasperGold, Synopsys VC Formal, Mentor Questa Formal
- **Debug**: Waveform viewers show assertion failures

**Enable assertions:**
```bash
# VCS
vcs -sverilog -assert svaext

# Xcelium  
xrun -assert

# Questa
vlog -sv +acc
```

---

## References

### Books
- **"SystemVerilog Assertions Handbook"** - Ben Cohen et al. (THE reference)
- **"A Practical Introduction to PSL"** - Cindy Eisner & Dana Fisman
- **"SystemVerilog Assertions and Functional Coverage"** - Ashok Mehta

### Standards
- **IEEE 1800-2017**: SystemVerilog (includes SVA)
- **IEEE 1850**: PSL (Property Specification Language)

### Online
- **Doulos**: https://www.doulos.com/knowhow/sysverilog/tutorial/assertions/
- **Verification Academy**: https://verificationacademy.com/topics/assertion-based-verification
- **DVCon Papers**: Papers on assertion methodology

---

**Last Updated**: January 2026  
**Maintainer**: System Verilog Workshop
