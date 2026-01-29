# 09 - Formal Verification

This directory contains SystemVerilog Assertions (SVA), formal properties, and proof examples for verifying digital designs using formal verification techniques. Formal verification provides mathematical proof of correctness, complementing traditional simulation-based verification.

## Table of Contents

- [Overview](#overview)
- [Directory Structure](#directory-structure)
- [What is Formal Verification?](#what-is-formal-verification)
- [Topics Covered](#topics-covered)
- [Key Concepts](#key-concepts)
- [Formal Tools](#formal-tools)
- [Learning Path](#learning-path)
- [References](#references)

---

## Overview

**Formal verification** uses mathematical techniques to prove or disprove the correctness of a design with respect to a formal specification. Unlike simulation, which can only test specific scenarios, formal verification exhaustively explores all possible states (within bounds).

### Why Formal Verification?

| Aspect | Simulation | Formal Verification |
|--------|-----------|-------------------|
| **Coverage** | Tests specific scenarios | Exhaustive (within bounds) |
| **Bugs Found** | May miss corner cases | Finds all bugs in scope |
| **Runtime** | Fast for directed tests | Can be slow/infinite |
| **Complexity** | Any design | Better for control logic |
| **Confidence** | Statistical | Mathematical proof |

**Best Use Cases for Formal:**
- Protocol compliance (AXI, I2C, etc.)
- Control logic (arbiters, FSMs)
- Safety-critical properties (mutex, deadlock-freedom)
- Data integrity (FIFOs, memories)
- Clock domain crossing (CDC)
- Corner case discovery

---

## Directory Structure

```
09_formal_verification/
├── README.md                        # This file
├── basic_properties/
│   ├── safety_properties.sv         # "Bad thing never happens"
│   ├── liveness_properties.sv       # "Good thing eventually happens"
│   ├── fairness_properties.sv       # Fair arbitration
│   └── README.md
├── protocol_compliance/
│   ├── axi_formal_properties.sv     # AXI protocol checks
│   ├── apb_formal_properties.sv     # APB protocol checks
│   ├── handshake_formal.sv          # Valid-ready handshake
│   ├── i2c_formal_properties.sv     # I2C start/stop conditions
│   └── README.md
├── data_integrity/
│   ├── fifo_formal_proof.sv         # Prove FIFO correctness
│   ├── counter_formal.sv            # Prove counter bounds
│   ├── memory_formal.sv             # Memory read/write consistency
│   └── README.md
├── bounded_proofs/
│   ├── mutex_proof.sv               # Mutual exclusion proof
│   ├── arbiter_proof.sv             # Fair arbitration proof
│   ├── deadlock_freedom.sv          # Prove no deadlock
│   └── README.md
├── cover_properties/
│   ├── reachability.sv              # Prove state is reachable
│   ├── corner_cases.sv              # Reach interesting scenarios
│   ├── protocol_sequences.sv        # Valid transaction sequences
│   └── README.md
├── assume_guarantee/
│   ├── environment_assumptions.sv   # Assume valid inputs
│   ├── interface_contracts.sv       # Module contracts
│   ├── compositional_proof.sv       # Proof composition
│   └── README.md
├── equivalence/
│   ├── sequential_equivalence.sv    # Before/after optimization
│   ├── fsm_equivalence.sv           # Different FSM encodings
│   ├── pipeline_equivalence.sv      # Pipelined vs non-pipelined
│   └── README.md
└── case_studies/
    ├── cdc_formal/                  # CDC correctness
    │   ├── gray_code_proof.sv       # Prove gray code properties
    │   ├── handshake_sync_proof.sv  # 2-FF synchronizer + handshake
    │   ├── mcp_proof.sv             # Multi-cycle path
    │   └── README.md
    ├── fifo_full_proof/
    │   ├── fifo_model.sv
    │   ├── fifo_properties.sv
    │   ├── formal_tb.sv
    │   └── README.md
    └── arbiter_fairness/
        ├── rr_arbiter.sv
        ├── fairness_proof.sv
        └── README.md
```

---

## What is Formal Verification?

### Types of Formal Verification

1. **Model Checking (Property Checking)**
   - Check if design satisfies properties
   - Uses bounded or unbounded algorithms
   - Most common in RTL verification

2. **Equivalence Checking**
   - Prove two designs are functionally equivalent
   - Used after synthesis, optimization, ECO

3. **Theorem Proving**
   - Mathematical proofs using logic
   - Requires significant manual effort
   - Used for algorithms, not RTL

### Formal Property Types

#### **Safety Properties** ("Nothing bad happens")
- Mutual exclusion
- No overflow/underflow
- Protocol compliance
- "Always P"

#### **Liveness Properties** ("Something good eventually happens")
- Request eventually granted
- Eventual progress
- Deadlock-freedom
- "Eventually Q"

#### **Fairness Properties**
- Fair scheduling
- No starvation
- Bounded waiting

---

## Topics Covered

### 1. Basic Properties

#### **Safety Properties**

```systemverilog
// Example: FIFO never overflows
property no_overflow;
    @(posedge clk) disable iff (!rst_n)
    full |-> !push;
endproperty
assert property (no_overflow) else $error("FIFO overflow");

// Example: Mutual exclusion
property mutex;
    @(posedge clk) disable iff (!rst_n)
    !(grant_a && grant_b);
endproperty
assert property (mutex) else $error("Both granted!");
```

#### **Liveness Properties**

```systemverilog
// Example: Request eventually granted
property eventual_grant;
    @(posedge clk) disable iff (!rst_n)
    req |-> ##[1:$] grant;
endproperty
assert property (eventual_grant) else $error("Starvation");

// Note: Unbounded liveness requires fairness assumptions
```

---

### 2. Protocol Compliance

Formal verification excels at proving protocol compliance.

#### **AXI Protocol Properties**

```systemverilog
module axi_write_channel_properties (
    input logic        aclk,
    input logic        aresetn,
    input logic        awvalid,
    input logic        awready,
    input logic [31:0] awaddr,
    input logic        wvalid,
    input logic        wready,
    input logic        wlast
);

    // Property: AWVALID once high, must stay high until AWREADY
    property awvalid_stable;
        @(posedge aclk) disable iff (!aresetn)
        awvalid && !awready |=> awvalid;
    endproperty
    assert property (awvalid_stable) else $error("AWVALID dropped");

    // Property: AWADDR must be stable while AWVALID && !AWREADY
    property awaddr_stable;
        @(posedge aclk) disable iff (!aresetn)
        awvalid && !awready |=> $stable(awaddr);
    endproperty
    assert property (awaddr_stable) else $error("AWADDR changed");

    // Property: Write data must come after write address
    property w_after_aw;
        @(posedge aclk) disable iff (!aresetn)
        wvalid |-> $past(awvalid && awready, 1) || awvalid;
    endproperty
    // Note: Depends on specific AXI implementation

    // Cover: Successful write transaction
    sequence write_addr_handshake;
        awvalid && awready;
    endsequence
    
    sequence write_data_handshake;
        wvalid && wready && wlast;
    endsequence
    
    cover property (@(posedge aclk) 
        write_addr_handshake ##[0:10] write_data_handshake);

endmodule
```

#### **Handshake Protocol**

```systemverilog
// Valid-Ready handshake properties
module handshake_formal (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic ready,
    input logic [31:0] data
);

    // Property: Valid stays high until ready
    property valid_stable;
        @(posedge clk) disable iff (!rst_n)
        valid && !ready |=> valid;
    endproperty
    assert property (valid_stable);

    // Property: Data stable while valid && !ready
    property data_stable;
        @(posedge clk) disable iff (!rst_n)
        valid && !ready |=> $stable(data);
    endproperty
    assert property (data_stable);

    // Cover: Back-to-back transfers
    cover property (@(posedge clk) disable iff (!rst_n)
        (valid && ready) ##1 (valid && ready));

endmodule
```

---

### 3. Data Integrity

Prove that data is correctly stored and retrieved.

#### **FIFO Formal Proof**

```systemverilog
module fifo_formal_properties #(
    parameter DEPTH = 8,
    parameter WIDTH = 32
) (
    input logic clk,
    input logic rst_n,
    input logic push,
    input logic pop,
    input logic [WIDTH-1:0] data_in,
    input logic [WIDTH-1:0] data_out,
    input logic full,
    input logic empty
);

    // Property: Never overflow
    property no_overflow;
        @(posedge clk) disable iff (!rst_n)
        full |-> !push;
    endproperty
    assert property (no_overflow) else $error("FIFO overflow");

    // Property: Never underflow
    property no_underflow;
        @(posedge clk) disable iff (!rst_n)
        empty |-> !pop;
    endproperty
    assert property (no_underflow) else $error("FIFO underflow");

    // Property: Full and empty are mutually exclusive
    property full_empty_mutex;
        @(posedge clk) disable iff (!rst_n)
        !(full && empty) || (DEPTH == 1);
    endproperty
    assert property (full_empty_mutex);

    // Data integrity with shadow FIFO
    logic [WIDTH-1:0] shadow_mem [DEPTH];
    logic [$clog2(DEPTH):0] wr_ptr, rd_ptr;
    logic [$clog2(DEPTH):0] count;
    
    // Shadow write
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= 0;
        end else if (push && !full) begin
            shadow_mem[wr_ptr[$clog2(DEPTH)-1:0]] <= data_in;
            wr_ptr <= wr_ptr + 1;
        end
    end
    
    // Shadow read
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_ptr <= 0;
        end else if (pop && !empty) begin
            rd_ptr <= rd_ptr + 1;
        end
    end
    
    assign count = wr_ptr - rd_ptr;
    
    // Property: Data matches shadow FIFO
    property data_integrity;
        @(posedge clk) disable iff (!rst_n)
        pop && !empty |-> data_out == shadow_mem[rd_ptr[$clog2(DEPTH)-1:0]];
    endproperty
    assert property (data_integrity) else $error("Data mismatch");
    
    // Property: Count matches full/empty
    property count_full;
        @(posedge clk) disable iff (!rst_n)
        (count == DEPTH) == full;
    endproperty
    assert property (count_full);
    
    property count_empty;
        @(posedge clk) disable iff (!rst_n)
        (count == 0) == empty;
    endproperty
    assert property (count_empty);
    
    // Cover: Reach full state
    cover property (@(posedge clk) full);
    
    // Cover: Back-to-back transactions
    cover property (@(posedge clk) push ##1 pop);

endmodule
```

---

### 4. Bounded Proofs

#### **Mutual Exclusion Proof**

```systemverilog
module mutex_formal (
    input logic clk,
    input logic rst_n,
    input logic req_a,
    input logic req_b,
    input logic grant_a,
    input logic grant_b
);

    // Safety property: Mutual exclusion
    property mutex;
        @(posedge clk) disable iff (!rst_n)
        !(grant_a && grant_b);
    endproperty
    assert property (mutex) else $error("Both granted!");

    // Liveness: Request eventually granted
    // Note: Requires fairness assumption
    property eventual_grant_a;
        @(posedge clk) disable iff (!rst_n)
        req_a |-> ##[1:$] grant_a;
    endproperty
    assert property (eventual_grant_a) else $error("Starvation of A");
    
    property eventual_grant_b;
        @(posedge clk) disable iff (!rst_n)
        req_b |-> ##[1:$] grant_b;
    endproperty
    assert property (eventual_grant_b) else $error("Starvation of B");

    // Cover: Alternating grants
    cover property (@(posedge clk) disable iff (!rst_n)
        grant_a ##1 !grant_a ##1 grant_b ##1 !grant_b ##1 grant_a);

    // Cover: Both requesting
    cover property (@(posedge clk) disable iff (!rst_n)
        req_a && req_b);

endmodule
```

#### **Arbiter Fairness Proof**

```systemverilog
module arbiter_fairness_formal (
    input logic clk,
    input logic rst_n,
    input logic [3:0] req,
    input logic [3:0] grant
);

    // One-hot grant
    property onehot_grant;
        @(posedge clk) disable iff (!rst_n)
        $onehot0(grant);  // At most one hot
    endproperty
    assert property (onehot_grant);

    // Only grant if requested
    property grant_when_req;
        @(posedge clk) disable iff (!rst_n)
        (grant != 0) |-> ((grant & req) != 0);
    endproperty
    assert property (grant_when_req);

    // No starvation (bounded fairness)
    // If continuously requesting, must be granted within N cycles
    parameter MAX_WAIT = 10;
    
    property no_starvation_0;
        @(posedge clk) disable iff (!rst_n)
        req[0] |-> ##[1:MAX_WAIT] grant[0];
    endproperty
    assert property (no_starvation_0) else $error("Starvation req[0]");
    
    // Repeat for other requesters...

    // Cover: All requesters active
    cover property (@(posedge clk) disable iff (!rst_n)
        req == 4'b1111);

endmodule
```

---

### 5. Cover Properties

Cover properties help verify that interesting scenarios are reachable.

```systemverilog
// Example: State machine reachability
module fsm_cover (
    input logic clk,
    input logic rst_n,
    input logic [2:0] state
);
    parameter IDLE   = 3'b001;
    parameter ACTIVE = 3'b010;
    parameter DONE   = 3'b100;

    // Cover: Reach all states
    cover property (@(posedge clk) disable iff (!rst_n)
        state == IDLE);
    cover property (@(posedge clk) disable iff (!rst_n)
        state == ACTIVE);
    cover property (@(posedge clk) disable iff (!rst_n)
        state == DONE);

    // Cover: State transitions
    cover property (@(posedge clk) disable iff (!rst_n)
        (state == IDLE) ##1 (state == ACTIVE));
    cover property (@(posedge clk) disable iff (!rst_n)
        (state == ACTIVE) ##1 (state == DONE));
    cover property (@(posedge clk) disable iff (!rst_n)
        (state == DONE) ##1 (state == IDLE));

    // Cover: Quick path through FSM
    cover property (@(posedge clk) disable iff (!rst_n)
        (state == IDLE) ##1 (state == ACTIVE) ##1 (state == DONE));

endmodule
```

---

### 6. Assume-Guarantee Reasoning

Use assumptions to constrain inputs and guarantees to prove outputs.

```systemverilog
module assume_guarantee_example (
    input logic clk,
    input logic rst_n,
    input logic req,
    input logic ack
);

    // ASSUME: Valid input behavior
    // Request stays high until acknowledged
    assume property (@(posedge clk) disable iff (!rst_n)
        req && !ack |=> req);

    // ASSUME: No simultaneous req and ack on first cycle
    assume property (@(posedge clk) disable iff (!rst_n)
        $rose(req) |-> !ack);

    // GUARANTEE: Ack comes within bounded time
    property ack_within_bound;
        @(posedge clk) disable iff (!rst_n)
        req |-> ##[1:10] ack;
    endproperty
    assert property (ack_within_bound);

    // GUARANTEE: No spurious acks
    property no_spurious_ack;
        @(posedge clk) disable iff (!rst_n)
        ack |-> req;
    endproperty
    assert property (no_spurious_ack);

endmodule
```

---

### 7. Clock Domain Crossing (CDC)

CDC is a critical area for formal verification.

#### **Gray Code Proof**

```systemverilog
module gray_code_formal (
    input logic [3:0] binary,
    input logic [3:0] gray
);

    // Assume gray is encoded correctly from binary
    assume property (gray == (binary ^ (binary >> 1)));

    // Prove: Adjacent gray codes differ by exactly 1 bit
    logic [3:0] binary_next = binary + 1;
    logic [3:0] gray_next = binary_next ^ (binary_next >> 1);
    
    property one_bit_change;
        $countones(gray ^ gray_next) == 1;
    endproperty
    assert property (one_bit_change);

    // Prove: Gray codes are unique (bijection)
    logic [3:0] other_binary;
    assume property (other_binary != binary);
    logic [3:0] other_gray = other_binary ^ (other_binary >> 1);
    
    assert property (gray != other_gray) else $error("Not unique!");

    // Cover: All transitions
    cover property (binary == 4'hF ##1 binary == 4'h0);

endmodule
```

#### **Two-Flop Synchronizer**

```systemverilog
module two_flop_sync_formal (
    input  logic clk_src,
    input  logic clk_dst,
    input  logic rst_n,
    input  logic data_in,
    input  logic sync_out
);

    // Model the synchronizer
    logic ff1, ff2;
    
    always_ff @(posedge clk_dst or negedge rst_n) begin
        if (!rst_n) begin
            ff1 <= 0;
            ff2 <= 0;
        end else begin
            ff1 <= data_in;
            ff2 <= ff1;
        end
    end
    
    assign sync_out = ff2;

    // Property: Output eventually matches stable input
    // (This requires careful CDC constraints)
    
    // Cover: Transition captured
    cover property (@(posedge clk_dst) disable iff (!rst_n)
        $rose(sync_out));

endmodule
```

---

## Key Concepts

### Bounded vs Unbounded Model Checking

| Type | Description | Use Case |
|------|-------------|----------|
| **Bounded** | Checks up to N cycles | Most practical proofs |
| **Unbounded** | Exhaustive proof | Simple designs, induction |
| **K-induction** | Base + inductive step | Extend bounded to unbounded |

### Formal Convergence

- **Proven**: Property holds for all reachable states
- **Violated**: Counterexample found (bug!)
- **Inconclusive**: Ran out of time/memory
- **Vacuous**: Property trivially true (bad property)

### Writing Good Properties

✅ **DO:**
- Keep properties simple and focused
- Use meaningful names
- Add error messages
- Test properties with simulation first
- Use cover to verify properties are exercised

❌ **DON'T:**
- Write overly complex properties
- Forget disable iff (reset)
- Assume without verification
- Skip cover properties
- Ignore vacuous passes

---

## Formal Tools

### Commercial Tools

1. **Cadence JasperGold**
   - Leading formal tool
   - Formal Property Verification (FPV)
   - Formal Equivalence Checking
   - Comprehensive app library (CDC, RDC, X-propagation)

2. **Synopsys VC Formal**
   - Property verification
   - Sequential equivalence checking
   - Integrated with VCS

3. **Siemens Questa Formal**
   - Formal verification
   - Integrated with Questa simulator
   - Hybrid formal-simulation

4. **Mentor SLEC**
   - Sequential logic equivalence checker
   - Used after optimizations

### Open-Source Tools

1. **SymbiYosys**
   - Open-source formal framework
   - Uses multiple engines (ABC, Z3, Yices)
   - Good for learning

2. **ABC**
   - Synthesis and verification
   - Sequential equivalence checking

### Property Languages

- **SystemVerilog Assertions (SVA)**: Industry standard
- **PSL (Property Specification Language)**: IEEE standard
- **OVL (Open Verification Library)**: Pre-defined assertions

---

## Learning Path

### Beginner (Week 1-2)
1. Learn **SVA syntax** (sequences, properties)
2. Write simple **safety properties**
3. Practice with **immediate assertions**
4. Understand **cover properties**

### Intermediate (Week 3-4)
5. **Protocol properties** (handshakes, AXI)
6. **Data integrity** proofs (counters, FIFOs)
7. **Assume-guarantee** reasoning
8. Tool practice (JasperGold/SymbiYosys)

### Advanced (Week 5-8)
9. **Liveness properties** and fairness
10. **CDC formal verification**
11. **Equivalence checking**
12. **Complex case studies** (cache, arbiter)

### Expert (Ongoing)
13. **Compositional verification**
14. **Abstraction** techniques
15. **Custom proof strategies**
16. **Industry applications**

---

## Methodology

### Formal Verification Flow

1. **Define Properties**
   - What should the design do?
   - Safety, liveness, protocol compliance

2. **Add Constraints (Assumptions)**
   - Valid input behavior
   - Environmental constraints
   - Initial state constraints

3. **Run Formal Tool**
   - Bounded model checking
   - Set depth/timeout
   - Check convergence

4. **Analyze Results**
   - **Proven**: Great!
   - **CEX**: Debug counterexample
   - **Inconclusive**: Increase bounds, add constraints

5. **Iterate**
   - Refine properties
   - Add helper assertions
   - Decompose complex proofs

### Integration with Simulation

Formal complements, not replaces, simulation:

| Method | Best For |
|--------|----------|
| **Simulation** | Full-chip verification, performance, complex protocols |
| **Formal** | Control logic, corner cases, protocol compliance |
| **Hybrid** | Formal for critical blocks, simulation for integration |

---

## Common Pitfalls

1. **Vacuous Pass**: Property never exercised
   - Fix: Add cover properties
   
2. **Over-constrained Assumptions**: Make problem trivial
   - Fix: Verify assumptions with cover

3. **Under-constrained**: State space explosion
   - Fix: Add reasonable assumptions

4. **Tool Capacity**: Too complex for formal
   - Fix: Decompose, use abstraction

5. **Wrong Property**: Doesn't capture intent
   - Fix: Review with design spec

---

## Best Practices

### Property Writing

```systemverilog
// Good: Clear, focused property
property req_before_ack;
    @(posedge clk) disable iff (!rst_n)
    ack |-> $past(req);
endproperty
assert property (req_before_ack) else $error("Ack without req");

// Bad: Overly complex, hard to debug
property complex_check;
    @(posedge clk) disable iff (!rst_n)
    (req && (state == IDLE || state == WAIT) && !busy) |->
    ##[1:5] (ack || error) ##[1:3] done;
endproperty
```

### Layered Approach

1. **Basic properties**: No overflow, mutex
2. **Protocol properties**: Handshakes, stability
3. **Data properties**: Integrity, ordering
4. **System properties**: Liveness, fairness

---

## Case Studies

### 1. FIFO Correctness
- No overflow/underflow
- Data integrity (in order)
- Flag correctness (full/empty)
- Corner cases (simultaneous push/pop)

### 2. Arbiter Verification
- Mutual exclusion
- Fair arbitration
- No starvation
- Grant only when requested

### 3. CDC Verification
- Gray code properties
- Synchronizer behavior
- Handshake protocols
- FIFO pointer synchronization

### 4. AXI Protocol
- Handshake stability
- Address/data relationship
- Response ordering
- Outstanding transactions

---

## References

### Books
- "SystemVerilog Assertions and Functional Coverage" - Vijayaraghavan & Ramanathan
- "A Practical Introduction to PSL" - Cindy Eisner & Dana Fisman
- "Formal Verification: An Essential Toolkit" - Erik Seligman et al.

### Standards
- **IEEE 1800**: SystemVerilog (includes SVA)
- **IEEE 1850**: Property Specification Language (PSL)

### Papers
- "Bounded Model Checking" - Clarke et al.
- "Symbolic Model Checking: 10^20 States and Beyond" - Burch et al.

### Online Resources
- Verification Academy (Cadence)
- Synopsys Formal Verification Training
- SymbiYosys Documentation
- DVClub Formal Verification Presentations

### Tool Documentation
- JasperGold User Guide
- VC Formal Documentation
- SymbiYosys Manual

---

## Contributing

When adding examples:
1. Include clear property description
2. Provide design under verification
3. Show expected results (proven/CEX)
4. Document assumptions
5. Add cover properties
6. Update this README

---

## Tool Scripts

### Example SymbiYosys Script (.sby)

```ini
[tasks]
prove
cover

[options]
prove: mode prove
prove: depth 20
cover: mode cover
cover: depth 15

[engines]
smtbmc z3

[script]
read -formal design.sv
read -formal properties.sv
prep -top design_top

[files]
design.sv
properties.sv
```

### Example JasperGold TCL

```tcl
# Load design
analyze -sv design.sv
elaborate -top design_top

# Set up clocks and resets
clock clk
reset -expression !rst_n

# Prove all properties
prove -all

# Generate report
report -file formal_report.txt
```

---

## Exercises

### Beginner
1. Write assertions for a simple counter (overflow, reset)
2. Verify a 2-to-1 mux (output matches selected input)
3. Prove mutex for a simple arbiter

### Intermediate
4. Full FIFO verification with data integrity
5. AXI-Lite protocol compliance checker
6. Round-robin arbiter fairness proof

### Advanced
7. Gray code counter CDC proof
8. Pipeline equivalence checking
9. Cache coherence properties

---

**Last Updated**: January 2026
**Maintainer**: System Verilog Workshop

---

## Quick Reference

### Common SVA Operators

| Operator | Meaning | Example |
|----------|---------|---------|
| `##N` | Delay by N cycles | `a ##1 b` (b follows a by 1 cycle) |
| `##[m:n]` | Delay range | `a ##[1:5] b` (b within 1-5 cycles) |
| `|->` | Implication | `a |-> b` (if a, then b) |
| `|=>` | Implication with delay | `a |=> b` (if a, then b next cycle) |
| `$past` | Previous value | `$past(sig, 1)` (sig 1 cycle ago) |
| `$stable` | Value unchanged | `$stable(data)` |
| `$rose` | Rising edge | `$rose(valid)` |
| `$fell` | Falling edge | `$fell(ready)` |
| `throughout` | Condition holds | `a throughout b` |
| `within` | Sequence within | `a within b` |

### Assertion Template

```systemverilog
// Standard assertion template
property prop_name;
    @(posedge clk) disable iff (!rst_n)
    precondition |-> consequence;
endproperty

assert property (prop_name) else $error("Description");
cover property (prop_name);
```
