# 01 - Synthesizable RTL Design

This directory covers synthesizable RTL (Register Transfer Level) design fundamentals. Learn to write clean, efficient, and synthesis-friendly SystemVerilog code for ASIC and FPGA implementations.

## Table of Contents

- [Overview](#overview)
- [Directory Structure](#directory-structure)
- [RTL Design Principles](#rtl-design-principles)
- [Coding Guidelines](#coding-guidelines)
- [Common Patterns](#common-patterns)
- [Learning Path](#learning-path)
- [References](#references)

---

## Overview

**RTL (Register Transfer Level)** describes digital circuits as:
- **Registers**: Storage elements (flip-flops)
- **Combinational logic**: Logic between registers
- **Data transfer**: Movement of data through pipeline

**Key Goal**: Write code that synthesizes to efficient, correct hardware.

---

## Directory Structure

```
01_synthesizable_rtl/
├── README.md
├── combinational/
│   ├── mux_decoder.sv
│   ├── encoder_priority.sv
│   ├── arithmetic.sv
│   ├── comparators.sv
│   └── README.md
├── sequential/
│   ├── registers.sv
│   ├── counters.sv
│   ├── shift_registers.sv
│   ├── state_machines.sv
│   └── README.md
├── memory/
│   ├── single_port_ram.sv
│   ├── dual_port_ram.sv
│   ├── fifo_sync.sv
│   └── README.md
├── finite_state_machines/
│   ├── moore_fsm.sv
│   ├── mealy_fsm.sv
│   ├── one_hot_fsm.sv
│   ├── gray_fsm.sv
│   └── README.md
├── pipelining/
│   ├── simple_pipeline.sv
│   ├── pipeline_with_stall.sv
│   ├── pipeline_flush.sv
│   └── README.md
└── synthesis_examples/
    ├── resource_sharing.sv
    ├── operator_precedence.sv
    ├── inference_examples.sv
    └── README.md
```

---

## RTL Design Principles

### 1. Synchronous Design

**Everything happens on clock edges** (mostly positive edge):

```systemverilog
// Good: Synchronous design
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        counter <= '0;
    else
        counter <= counter + 1;
end

// Avoid: Asynchronous logic (except reset)
```

**Benefits:**
- Predictable timing
- Easier synthesis
- Standard design flow
- Clock gating friendly

---

### 2. Separate Combinational and Sequential Logic

```systemverilog
// Combinational logic
always_comb begin
    next_state = state;
    case (state)
        IDLE:   if (start) next_state = ACTIVE;
        ACTIVE: if (done)  next_state = IDLE;
    endcase
end

// Sequential logic (registers)
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        state <= IDLE;
    else
        state <= next_state;
end
```

**Benefits:**
- Clear separation of concerns
- Easier to debug
- Avoids latches
- Synthesis tool friendly

---

### 3. Reset Strategy

#### **Asynchronous Reset** (Most Common in ASIC)
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        data <= '0;  // Reset immediately
    else
        data <= data_in;
end
```

#### **Synchronous Reset**
```systemverilog
always_ff @(posedge clk) begin
    if (!rst_n)
        data <= '0;  // Reset on clock edge
    else
        data <= data_in;
end
```

| Aspect | Async Reset | Sync Reset |
|--------|-------------|------------|
| **Reset speed** | Immediate | One clock cycle |
| **Timing** | Special analysis | Normal data path |
| **Clock gating** | May conflict | Compatible |
| **Area** | Slightly more | Slightly less |

---

## Coding Guidelines

### Always Blocks

#### **always_ff** - Sequential (Registers)
```systemverilog
// Use for registers
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        q <= '0;
    else
        q <= d;
end
```

#### **always_comb** - Combinational Logic
```systemverilog
// Use for combinational logic
always_comb begin
    y = a & b | c;
    z = (x > 5) ? x - 5 : x;
end
```

#### **always_latch** - Latches (Avoid!)
```systemverilog
// Rarely used - explicit latch
always_latch begin
    if (enable)
        q <= d;
end
```

---

### Avoiding Latches

**Latches are usually unintentional and problematic!**

```systemverilog
// BAD: Infers latch (incomplete case)
always_comb begin
    case (sel)
        2'b00: out = a;
        2'b01: out = b;
        // Missing cases! Latch inferred
    endcase
end

// GOOD: Complete case
always_comb begin
    case (sel)
        2'b00: out = a;
        2'b01: out = b;
        2'b10: out = c;
        2'b11: out = d;
    endcase
end

// GOOD: Default case
always_comb begin
    case (sel)
        2'b00: out = a;
        2'b01: out = b;
        default: out = '0;
    endcase
end

// GOOD: Initialize output
always_comb begin
    out = '0;  // Default value
    case (sel)
        2'b00: out = a;
        2'b01: out = b;
    endcase
end
```

---

### Blocking vs Non-Blocking

| Context | Use | Reason |
|---------|-----|--------|
| **Sequential (always_ff)** | `<=` (non-blocking) | Parallel register updates |
| **Combinational (always_comb)** | `=` (blocking) | Sequential evaluation |

```systemverilog
// Sequential: Use <=
always_ff @(posedge clk) begin
    a <= b;
    b <= a;  // Swap! Both use old values
end

// Combinational: Use =
always_comb begin
    temp = a + b;
    result = temp * c;  // Uses new value of temp
end
```

---

## Common Patterns

### 1. Multiplexers

```systemverilog
// 2:1 Mux
module mux2to1 (
    input  logic       sel,
    input  logic [7:0] a, b,
    output logic [7:0] y
);
    assign y = sel ? b : a;
endmodule

// 4:1 Mux (case statement)
always_comb begin
    case (sel)
        2'b00: out = in0;
        2'b01: out = in1;
        2'b10: out = in2;
        2'b11: out = in3;
    endcase
end

// Parameterized N:1 Mux
module mux_n #(parameter WIDTH = 8, N = 4) (
    input  logic [$clog2(N)-1:0] sel,
    input  logic [WIDTH-1:0]     in [N],
    output logic [WIDTH-1:0]     out
);
    assign out = in[sel];
endmodule
```

---

### 2. Registers

```systemverilog
// Simple register
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        q <= '0;
    else
        q <= d;
end

// Register with enable
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        q <= '0;
    else if (en)
        q <= d;
end

// Register with load
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        q <= '0;
    else if (load)
        q <= load_value;
    else if (en)
        q <= d;
end
```

---

### 3. Counters

```systemverilog
// Up counter
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        count <= '0;
    else if (en)
        count <= count + 1;
end

// Up/Down counter with load
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        count <= '0;
    else if (load)
        count <= load_value;
    else if (en) begin
        if (up_down)
            count <= count + 1;
        else
            count <= count - 1;
    end
end

// Counter with terminal count
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        count <= '0;
        tc <= 1'b0;
    end else if (en) begin
        if (count == MAX_COUNT) begin
            count <= '0;
            tc <= 1'b1;
        end else begin
            count <= count + 1;
            tc <= 1'b0;
        end
    end
end
```

---

### 4. Shift Registers

```systemverilog
// Simple shift register
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        shift_reg <= '0;
    else
        shift_reg <= {shift_reg[WIDTH-2:0], serial_in};
end

// Shift register with load
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        shift_reg <= '0;
    else if (load)
        shift_reg <= parallel_in;
    else if (shift_en)
        shift_reg <= {shift_reg[WIDTH-2:0], serial_in};
end

// Barrel shifter (combinational)
always_comb begin
    case (shift_amount)
        3'd0: shifted = data;
        3'd1: shifted = {data[30:0], 1'b0};
        3'd2: shifted = {data[29:0], 2'b0};
        // ... etc
    endcase
end
```

---

### 5. State Machines

#### **Moore FSM** (outputs depend only on state)

```systemverilog
typedef enum logic [1:0] {
    IDLE   = 2'b00,
    START  = 2'b01,
    RUN    = 2'b10,
    DONE   = 2'b11
} state_t;

state_t state, next_state;

// State register
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        state <= IDLE;
    else
        state <= next_state;
end

// Next state logic (combinational)
always_comb begin
    next_state = state;  // Default: stay in current state
    case (state)
        IDLE:  if (go)   next_state = START;
        START: next_state = RUN;
        RUN:   if (done) next_state = DONE;
        DONE:  next_state = IDLE;
    endcase
end

// Output logic (combinational, depends only on state)
always_comb begin
    // Defaults
    busy = 1'b0;
    complete = 1'b0;
    
    case (state)
        IDLE:  begin
            // Outputs for IDLE
        end
        START, RUN: begin
            busy = 1'b1;
        end
        DONE: begin
            complete = 1'b1;
        end
    endcase
end
```

#### **Mealy FSM** (outputs depend on state and inputs)

```systemverilog
// Outputs depend on current state AND inputs
always_comb begin
    next_state = state;
    output_signal = 1'b0;  // Default
    
    case (state)
        IDLE: begin
            if (input_a) begin
                next_state = ACTIVE;
                output_signal = 1'b1;  // Output changes with input
            end
        end
        ACTIVE: begin
            if (input_b)
                next_state = DONE;
            else
                output_signal = 1'b1;
        end
        DONE: next_state = IDLE;
    endcase
end
```

#### **One-Hot FSM**

```systemverilog
// One bit per state (faster, more area)
typedef enum logic [3:0] {
    IDLE   = 4'b0001,
    START  = 4'b0010,
    RUN    = 4'b0100,
    DONE   = 4'b1000
} state_onehot_t;

// Simpler next state logic
always_comb begin
    next_state = 4'b0000;
    case (1'b1)  // Check which bit is set
        state[0]: next_state = go ? START : IDLE;
        state[1]: next_state = RUN;
        state[2]: next_state = done ? DONE : RUN;
        state[3]: next_state = IDLE;
    endcase
end
```

---

### 6. Memory

#### **Single-Port RAM**

```systemverilog
module single_port_ram #(
    parameter WIDTH = 32,
    parameter DEPTH = 256
) (
    input  logic                    clk,
    input  logic                    we,
    input  logic [$clog2(DEPTH)-1:0] addr,
    input  logic [WIDTH-1:0]        din,
    output logic [WIDTH-1:0]        dout
);

    logic [WIDTH-1:0] mem [DEPTH];
    
    always_ff @(posedge clk) begin
        if (we)
            mem[addr] <= din;
        dout <= mem[addr];  // Read
    end

endmodule
```

#### **Dual-Port RAM**

```systemverilog
module dual_port_ram #(
    parameter WIDTH = 32,
    parameter DEPTH = 256
) (
    input  logic                     clk,
    // Port A (write)
    input  logic                     we_a,
    input  logic [$clog2(DEPTH)-1:0] addr_a,
    input  logic [WIDTH-1:0]         din_a,
    output logic [WIDTH-1:0]         dout_a,
    // Port B (read)
    input  logic [$clog2(DEPTH)-1:0] addr_b,
    output logic [WIDTH-1:0]         dout_b
);

    logic [WIDTH-1:0] mem [DEPTH];
    
    // Port A
    always_ff @(posedge clk) begin
        if (we_a)
            mem[addr_a] <= din_a;
        dout_a <= mem[addr_a];
    end
    
    // Port B
    always_ff @(posedge clk) begin
        dout_b <= mem[addr_b];
    end

endmodule
```

---

### 7. Pipelining

```systemverilog
// 3-stage pipeline
module pipeline_3stage (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [31:0] a, b,
    output logic [31:0] result
);

    logic [31:0] stage1, stage2;
    
    // Stage 1: Add
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            stage1 <= '0;
        else
            stage1 <= a + b;
    end
    
    // Stage 2: Multiply
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            stage2 <= '0;
        else
            stage2 <= stage1 * 3;
    end
    
    // Stage 3: Subtract
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            result <= '0;
        else
            result <= stage2 - 5;
    end

endmodule
```

**Benefits:**
- Higher clock frequency (shorter critical path)
- Increased throughput
- More latency (trade-off)

---

## Synthesis Considerations

### What Synthesizes?

✅ **Synthesizable:**
- `always_ff`, `always_comb`, `always_latch`
- `assign` statements
- `if-else`, `case`
- Arithmetic operators
- Comparison operators
- Logical operators
- Concatenation

❌ **Not Synthesizable:**
- `initial` blocks (except for simulation setup)
- `#delay` (delays)
- `wait` statements
- `forever`, `repeat` (in RTL)
- `$display`, `$monitor` (simulation only)
- Real numbers, floating point (generally)
- File I/O

---

### Operator Inference

```systemverilog
// Adder
assign sum = a + b;  // Infers adder

// Multiplier (expensive!)
assign product = a * b;  // Infers multiplier

// Comparator
assign greater = (a > b);  // Infers comparator

// Mux
assign out = sel ? a : b;  // Infers 2:1 mux

// Priority encoder
always_comb begin
    if (req[3])      grant = 4'b1000;
    else if (req[2]) grant = 4'b0100;
    else if (req[1]) grant = 4'b0010;
    else if (req[0]) grant = 4'b0001;
    else             grant = 4'b0000;
end
```

---

### Resource Sharing

```systemverilog
// Without resource sharing (2 adders)
always_comb begin
    if (sel)
        out = a + b;
    else
        out = c + d;
end

// With resource sharing (1 adder, 2 muxes)
always_comb begin
    temp_a = sel ? a : c;
    temp_b = sel ? b : d;
    out = temp_a + temp_b;
end
```

---

### Don't Cares

```systemverilog
// Use 'x' for don't care (optimization opportunity)
always_comb begin
    case (opcode)
        3'b000: result = a + b;
        3'b001: result = a - b;
        3'b010: result = a & b;
        default: result = 'x;  // Don't care
    endcase
end
```

---

## Design Patterns

### 1. Handshake Interface

```systemverilog
// Valid-ready handshake
module handshake_example (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [31:0] data_in,
    input  logic        valid_in,
    output logic        ready_out,
    output logic [31:0] data_out,
    output logic        valid_out,
    input  logic        ready_in
);

    // Transfer occurs when valid && ready
    logic [31:0] buffer;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            buffer <= '0;
            valid_out <= 1'b0;
        end else begin
            if (valid_in && ready_out) begin
                buffer <= data_in;
                valid_out <= 1'b1;
            end else if (ready_in && valid_out) begin
                valid_out <= 1'b0;
            end
        end
    end
    
    assign data_out = buffer;
    assign ready_out = !valid_out || ready_in;

endmodule
```

---

### 2. Parameterization

```systemverilog
module parameterized_module #(
    parameter WIDTH = 32,
    parameter DEPTH = 16,
    parameter type DATA_T = logic [WIDTH-1:0],
    localparam ADDR_WIDTH = $clog2(DEPTH)  // Computed
) (
    input  logic              clk,
    input  logic [ADDR_WIDTH-1:0] addr,
    input  DATA_T             data_in,
    output DATA_T             data_out
);
    // Implementation
endmodule
```

---

## Common Mistakes

### 1. Incomplete Sensitivity List (Pre-SystemVerilog)
```systemverilog
// BAD: Missing 'c' in sensitivity list
always @(a or b) begin  // Old Verilog style
    out = a & b | c;  // Changes to 'c' ignored!
end

// GOOD: Use always_comb (auto sensitivity)
always_comb begin
    out = a & b | c;
end
```

### 2. Multiple Drivers
```systemverilog
// BAD: Multiple drivers for 'out'
assign out = a & b;
always_comb out = c | d;  // Conflict!

// GOOD: Single driver
always_comb begin
    out = (sel) ? (a & b) : (c | d);
end
```

### 3. Combinational Loops
```systemverilog
// BAD: Combinational loop
assign a = b & c;
assign b = a | d;  // Loop!

// GOOD: Break loop with register
always_ff @(posedge clk)
    b <= a | d;
```

---

## Learning Path

### Week 1: Basics
- Combinational logic (mux, decoder, adder)
- Simple registers
- Basic counters

### Week 2: Sequential
- Shift registers
- FSMs (Moore, Mealy)
- State encoding

### Week 3: Advanced
- Pipelining
- Memory design
- Handshake protocols

### Week 4: Optimization
- Resource sharing
- Timing optimization
- Area/speed trade-offs

---

## Synthesis Flow

```
RTL (SystemVerilog)
        ↓
    [Synthesis]
        ↓
    Gate-level Netlist
        ↓
    [Place & Route]
        ↓
    Layout (GDSII)
```

**Synthesis checks:**
- Syntax errors
- Latch inference warnings
- Combinational loops
- Multiple drivers
- Timing violations

---

## Tools

**Synthesis:**
- Synopsys Design Compiler
- Cadence Genus
- Yosys (open-source)

**Simulation:**
- ModelSim/Questa
- VCS
- Xcelium
- Verilator

**Linting:**
- Synopsys Spyglass
- Cadence HAL
- Verilator (--lint-only)

---

## References

### Books
- **"RTL Modeling with SystemVerilog"** - Stuart Sutherland
- **"Digital Design and Computer Architecture"** - Harris & Harris
- **"Advanced ASIC Chip Synthesis"** - Himanshu Bhatnagar

### Standards
- **IEEE 1364**: Verilog
- **IEEE 1800**: SystemVerilog

### Online
- **ASIC World**: http://www.asic-world.com
- **ChipVerify**: https://www.chipverify.com
- **Nandland**: https://www.nandland.com

---

**Last Updated**: January 2026  
**Maintainer**: System Verilog Workshop
