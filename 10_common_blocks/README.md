# 10 - Common Digital Blocks

This directory contains frequently-used, reusable digital design building blocks that appear in most hardware projects. These are production-quality, parameterized components that you can use in real designs while learning best practices for RTL coding.

## Table of Contents

- [Overview](#overview)
- [Directory Structure](#directory-structure)
- [Block Categories](#block-categories)
- [Key Concepts](#key-concepts)
- [Design Guidelines](#design-guidelines)
- [Testing Strategy](#testing-strategy)
- [Learning Path](#learning-path)
- [References](#references)

---

## Overview

Common digital blocks are the building blocks of larger systems. Mastering these components is essential for:
- Understanding fundamental digital design patterns
- Building reusable IP libraries
- Learning synthesis-friendly coding styles
- Practicing verification techniques
- Understanding trade-offs (area, timing, power)

**Why Practice These Blocks?**
- **Universal**: Used in almost every digital design
- **Interview Favorites**: Commonly asked in technical interviews
- **Foundation**: Understanding these helps with complex designs
- **Reusable**: Build your own library of tested components

---

## Directory Structure

```
10_common_blocks/
├── README.md                          # This file
├── arbiters/
│   ├── fixed_priority_arbiter.sv
│   ├── round_robin_arbiter.sv
│   ├── weighted_round_robin.sv
│   ├── matrix_arbiter.sv              # Fully parallel
│   ├── arbiter_tb.sv
│   └── README.md
├── fifos/
│   ├── sync_fifo.sv                   # Single clock domain
│   ├── async_fifo.sv                  # Dual clock domain (gray code)
│   ├── showahead_fifo.sv              # Data appears immediately
│   ├── fwft_fifo.sv                   # First-Word-Fall-Through
│   ├── skid_buffer.sv                 # Pipeline register with backpressure
│   ├── fifo_tb.sv
│   └── README.md
├── synchronizers/
│   ├── two_flop_sync.sv               # Basic bit synchronizer
│   ├── handshake_sync.sv              # Req-ack synchronizer
│   ├── pulse_sync.sv                  # Pulse synchronizer
│   ├── mcp_fifo.sv                    # Multi-bit synchronizer
│   ├── reset_sync.sv                  # Reset synchronizer
│   └── README.md
├── counters/
│   ├── binary_counter.sv
│   ├── gray_counter.sv                # For async boundaries
│   ├── johnson_counter.sv
│   ├── lfsr.sv                        # Linear Feedback Shift Register
│   ├── one_hot_counter.sv
│   ├── modulo_counter.sv
│   └── README.md
├── muxes_decoders/
│   ├── parameterized_mux.sv
│   ├── one_hot_mux.sv
│   ├── binary_decoder.sv
│   ├── priority_encoder.sv
│   ├── one_hot_to_binary.sv
│   ├── thermometer_encoder.sv
│   └── README.md
├── error_detection/
│   ├── parity_generator.sv            # Even/odd parity
│   ├── crc_calculator.sv              # CRC-8, CRC-16, CRC-32
│   ├── hamming_encoder.sv             # Single-error correction
│   ├── hamming_decoder.sv             # SECDED
│   └── README.md
├── shifters/
│   ├── barrel_shifter.sv              # Combinational shifter
│   ├── serial_to_parallel.sv          # Deserializer
│   ├── parallel_to_serial.sv          # Serializer
│   ├── lfsr_scrambler.sv              # Data scrambling
│   └── README.md
├── edge_detectors/
│   ├── rising_edge_detect.sv
│   ├── falling_edge_detect.sv
│   ├── any_edge_detect.sv
│   ├── pulse_generator.sv
│   ├── pulse_stretcher.sv
│   └── README.md
├── delay_elements/
│   ├── fixed_delay.sv
│   ├── programmable_delay.sv
│   └── README.md
├── rate_adaptation/
│   ├── clock_divider.sv               # Integer division
│   ├── fractional_divider.sv
│   ├── rate_matcher.sv                # Elastic buffer
│   ├── gearbox.sv                     # Width + rate conversion
│   └── README.md
├── width_converters/
│   ├── upsizer.sv                     # Narrow to wide
│   ├── downsizer.sv                   # Wide to narrow
│   ├── axis_width_converter.sv        # AXI-Stream based
│   └── README.md
└── utility/
    ├── debouncer.sv                   # Button debouncing
    ├── timeout_counter.sv
    ├── watchdog_timer.sv
    ├── pulse_extender.sv
    ├── onehot_checker.sv
    └── README.md
```

---

## Block Categories

### 1. Arbiters

Arbiters resolve contention when multiple requesters compete for a shared resource.

#### **Fixed Priority Arbiter**
- Highest-numbered request always wins
- Simple but can starve low-priority requesters
- **Use case**: Interrupt controllers, time-critical systems

**Example:**
```systemverilog
module fixed_priority_arbiter #(
    parameter NUM_REQS = 4
) (
    input  logic                  clk,
    input  logic                  rst_n,
    input  logic [NUM_REQS-1:0]   req,
    output logic [NUM_REQS-1:0]   grant
);

    // Priority from MSB to LSB (higher index = higher priority)
    always_comb begin
        grant = '0;
        for (int i = NUM_REQS-1; i >= 0; i--) begin
            if (req[i]) begin
                grant[i] = 1'b1;
                break;
            end
        end
    end

endmodule
```

#### **Round-Robin Arbiter**
- Fair arbitration with rotating priority
- Prevents starvation
- **Use case**: Network routers, shared buses

**Key Concepts:**
- Track last granted requester
- Next priority position = (last_grant + 1) % N
- More complex than fixed priority

#### **Matrix Arbiter**
- Fully parallel, single-cycle arbitration
- Uses priority matrix (NxN flip-flops)
- **Trade-off**: Fast but high area (O(N²))

**Applications:**
| Arbiter Type | Latency | Area | Fairness | Use Case |
|--------------|---------|------|----------|----------|
| Fixed Priority | Low | Small | Poor | Critical requests |
| Round-Robin | Medium | Medium | Good | Shared resources |
| Weighted RR | Medium | Medium | Configurable | QoS systems |
| Matrix | Low | Large | Excellent | High-performance |

---

### 2. FIFOs

First-In-First-Out buffers for data storage and clock domain crossing.

#### **Synchronous FIFO**

```systemverilog
module sync_fifo #(
    parameter DEPTH = 16,
    parameter WIDTH = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    
    // Write interface
    input  logic             wr_en,
    input  logic [WIDTH-1:0] wr_data,
    output logic             full,
    output logic             almost_full,
    
    // Read interface
    input  logic             rd_en,
    output logic [WIDTH-1:0] rd_data,
    output logic             empty,
    output logic             almost_empty,
    
    // Status
    output logic [$clog2(DEPTH):0] count
);

    localparam ADDR_WIDTH = $clog2(DEPTH);
    
    // Memory
    logic [WIDTH-1:0] mem [DEPTH];
    
    // Pointers
    logic [ADDR_WIDTH:0] wr_ptr, rd_ptr;
    
    // Write logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= '0;
        end else if (wr_en && !full) begin
            mem[wr_ptr[ADDR_WIDTH-1:0]] <= wr_data;
            wr_ptr <= wr_ptr + 1;
        end
    end
    
    // Read logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_ptr <= '0;
        end else if (rd_en && !empty) begin
            rd_ptr <= rd_ptr + 1;
        end
    end
    
    assign rd_data = mem[rd_ptr[ADDR_WIDTH-1:0]];
    
    // Status flags
    assign count = wr_ptr - rd_ptr;
    assign empty = (count == 0);
    assign full = (count == DEPTH);
    assign almost_empty = (count == 1);
    assign almost_full = (count == DEPTH-1);

endmodule
```

#### **Asynchronous FIFO**
- **Critical for CDC**: Crossing clock domains safely
- **Gray code pointers**: Only 1 bit changes per increment
- **Synchronizers**: 2-FF synchronizer for pointer crossing
- **Empty/Full generation**: Compare synchronized pointers

**Key Challenge**: 
- Empty detection in read domain
- Full detection in write domain
- Metastability mitigation

**Example Gray Code Conversion:**
```systemverilog
function automatic logic [N-1:0] bin_to_gray(input logic [N-1:0] bin);
    return bin ^ (bin >> 1);
endfunction
```

#### **Skid Buffer**
- Single-entry FIFO with bypass
- Absorbs one cycle of backpressure
- **Use case**: Pipeline stages, AXI-Stream

---

### 3. Clock Domain Crossing (CDC) Synchronizers

Critical for multi-clock designs. CDC bugs are notoriously hard to debug.

#### **Two-Flop Synchronizer**

```systemverilog
module two_flop_sync (
    input  logic clk_dst,
    input  logic rst_n,
    input  logic data_in,
    output logic data_out
);

    (* ASYNC_REG = "TRUE" *) logic sync_ff1;
    (* ASYNC_REG = "TRUE" *) logic sync_ff2;
    
    always_ff @(posedge clk_dst or negedge rst_n) begin
        if (!rst_n) begin
            sync_ff1 <= 1'b0;
            sync_ff2 <= 1'b0;
        end else begin
            sync_ff1 <= data_in;
            sync_ff2 <= sync_ff1;
        end
    end
    
    assign data_out = sync_ff2;

endmodule
```

**Key Points:**
- **ASYNC_REG attribute**: Tells synthesis to keep FFs close
- **Only for single bits**: Multi-bit requires different approach
- **Metastability window**: MTBF = e^(T/τ) / (f_clk × f_data)
- **Reset value**: Consider startup behavior

#### **Handshake Synchronizer**

For multi-bit data crossing clock domains:
1. Source domain: Assert req when data ready
2. Destination domain: Synchronize req, assert ack
3. Source domain: Synchronize ack, deassert req
4. Destination domain: Deassert ack

**Latency**: 4+ clock cycles but guaranteed safe

#### **MCP FIFO (Multi-Cycle Path)**
- Asynchronous FIFO for fast-to-slow crossings
- Gray code counters
- Production-quality solution

---

### 4. Counters

#### **Binary Counter**
- Standard up/down counter
- With load, enable, terminal count

#### **Gray Counter**
```systemverilog
module gray_counter #(parameter WIDTH = 4) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             en,
    output logic [WIDTH-1:0] gray_count
);

    logic [WIDTH-1:0] bin_count;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            bin_count <= '0;
        else if (en)
            bin_count <= bin_count + 1;
    end
    
    assign gray_count = bin_count ^ (bin_count >> 1);

endmodule
```

**Use cases**: 
- Async FIFO pointers
- Any CDC counter application
- Minimizes glitching

#### **LFSR (Linear Feedback Shift Register)**
- Pseudo-random number generation
- CRC calculation
- Scrambling/descrambling
- Test pattern generation

**Example (Fibonacci LFSR):**
```systemverilog
// 8-bit LFSR with taps at positions 8, 6, 5, 4
module lfsr_8bit (
    input  logic       clk,
    input  logic       rst_n,
    input  logic       en,
    output logic [7:0] lfsr_out
);

    logic feedback;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            lfsr_out <= 8'hFF;  // Non-zero seed
        else if (en) begin
            feedback = lfsr_out[7] ^ lfsr_out[5] ^ lfsr_out[4] ^ lfsr_out[3];
            lfsr_out <= {lfsr_out[6:0], feedback};
        end
    end

endmodule
```

---

### 5. Error Detection and Correction

#### **Parity**
- **Even parity**: XOR of all bits
- **Odd parity**: XOR of all bits + 1
- **Detects**: Single-bit errors
- **Cannot correct**

```systemverilog
module parity_generator #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] data_in,
    output logic             even_parity,
    output logic             odd_parity
);

    assign even_parity = ^data_in;
    assign odd_parity = ~(^data_in);

endmodule
```

#### **CRC (Cyclic Redundancy Check)**
- Polynomial-based error detection
- Common: CRC-8, CRC-16, CRC-32
- **Use case**: Network packets, storage, serial protocols

**CRC-8 (polynomial 0x07):**
```systemverilog
module crc8 (
    input  logic       clk,
    input  logic       rst_n,
    input  logic       data_valid,
    input  logic [7:0] data_in,
    output logic [7:0] crc_out
);

    logic [7:0] crc;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            crc <= 8'h00;
        else if (data_valid) begin
            crc[0] <= data_in[7] ^ data_in[6] ^ data_in[0] ^ crc[0] ^ crc[6] ^ crc[7];
            crc[1] <= data_in[6] ^ data_in[1] ^ data_in[0] ^ crc[0] ^ crc[1] ^ crc[6];
            crc[2] <= data_in[6] ^ data_in[2] ^ data_in[1] ^ data_in[0] ^ crc[0] ^ crc[1] ^ crc[2] ^ crc[6];
            crc[3] <= data_in[7] ^ data_in[3] ^ data_in[2] ^ data_in[1] ^ crc[1] ^ crc[2] ^ crc[3] ^ crc[7];
            crc[4] <= data_in[4] ^ data_in[3] ^ data_in[2] ^ crc[2] ^ crc[3] ^ crc[4];
            crc[5] <= data_in[5] ^ data_in[4] ^ data_in[3] ^ crc[3] ^ crc[4] ^ crc[5];
            crc[6] <= data_in[6] ^ data_in[5] ^ data_in[4] ^ crc[4] ^ crc[5] ^ crc[6];
            crc[7] <= data_in[7] ^ data_in[6] ^ data_in[5] ^ crc[5] ^ crc[6] ^ crc[7];
        end
    end
    
    assign crc_out = crc;

endmodule
```

#### **Hamming Code**
- **SECDED**: Single Error Correction, Double Error Detection
- **Use case**: Memories, reliable storage
- Common: Hamming(7,4), Hamming(72,64)

---

### 6. Width Converters

Convert data width while maintaining throughput.

#### **Upsizer (Narrow → Wide)**
- Accumulate narrow words into wide word
- **Example**: 32-bit → 128-bit (4:1)

```systemverilog
module upsizer #(
    parameter NARROW_WIDTH = 32,
    parameter WIDE_WIDTH = 128  // Must be multiple of NARROW_WIDTH
) (
    input  logic                    clk,
    input  logic                    rst_n,
    
    // Narrow input
    input  logic [NARROW_WIDTH-1:0] narrow_data,
    input  logic                    narrow_valid,
    output logic                    narrow_ready,
    
    // Wide output
    output logic [WIDE_WIDTH-1:0]   wide_data,
    output logic                    wide_valid,
    input  logic                    wide_ready
);

    localparam RATIO = WIDE_WIDTH / NARROW_WIDTH;
    logic [$clog2(RATIO)-1:0] count;
    logic [WIDE_WIDTH-1:0] accumulator;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            count <= '0;
            accumulator <= '0;
            wide_valid <= 1'b0;
        end else begin
            wide_valid <= 1'b0;
            
            if (narrow_valid && narrow_ready) begin
                accumulator[count*NARROW_WIDTH +: NARROW_WIDTH] <= narrow_data;
                
                if (count == RATIO-1) begin
                    count <= '0;
                    wide_valid <= 1'b1;
                end else begin
                    count <= count + 1;
                end
            end else if (wide_valid && wide_ready) begin
                wide_valid <= 1'b0;
            end
        end
    end
    
    assign wide_data = accumulator;
    assign narrow_ready = !wide_valid || wide_ready;

endmodule
```

#### **Downsizer (Wide → Narrow)**
- Serializes wide word into narrow words
- **Example**: 128-bit → 32-bit (1:4)

---

### 7. Edge Detectors and Pulse Generators

#### **Rising Edge Detector**

```systemverilog
module rising_edge_detect (
    input  logic clk,
    input  logic rst_n,
    input  logic signal_in,
    output logic edge_detect
);

    logic signal_d;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            signal_d <= 1'b0;
        else
            signal_d <= signal_in;
    end
    
    assign edge_detect = signal_in & ~signal_d;

endmodule
```

#### **Pulse Generator**
- Generate fixed-width pulse from edge
- **Use case**: Interrupt generation, triggers

---

### 8. Utility Blocks

#### **Debouncer**
For mechanical switches (buttons):

```systemverilog
module debouncer #(
    parameter CLK_FREQ = 100_000_000,  // 100 MHz
    parameter DEBOUNCE_TIME = 20_000   // 20ms
) (
    input  logic clk,
    input  logic rst_n,
    input  logic button_in,
    output logic button_out
);

    localparam COUNT_MAX = CLK_FREQ / 1000 * DEBOUNCE_TIME / 1000;
    logic [$clog2(COUNT_MAX)-1:0] counter;
    logic button_sync;
    
    // Synchronize input
    logic sync1, sync2;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sync1 <= 1'b0;
            sync2 <= 1'b0;
        end else begin
            sync1 <= button_in;
            sync2 <= sync1;
        end
    end
    assign button_sync = sync2;
    
    // Debounce logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter <= '0;
            button_out <= 1'b0;
        end else begin
            if (button_sync != button_out) begin
                if (counter == COUNT_MAX-1) begin
                    button_out <= button_sync;
                    counter <= '0;
                end else begin
                    counter <= counter + 1;
                end
            end else begin
                counter <= '0;
            end
        end
    end

endmodule
```

#### **Watchdog Timer**
- Timeout detection
- System health monitoring
- **Use case**: Embedded systems, fault detection

---

## Key Concepts

### Design Trade-offs

Every block involves trade-offs:

| Aspect | Options | Considerations |
|--------|---------|----------------|
| **Area** | Combinational vs Sequential | Comb = more gates, Seq = registers + logic |
| **Speed** | Pipeline depth | More stages = higher f_max, more latency |
| **Power** | Clock gating, operand isolation | Complexity vs power savings |
| **Flexibility** | Parameterization | Generic vs optimized |

### Synthesis Considerations

**Good practices:**
- Avoid latches (except ICG)
- Register outputs when possible
- Use synchronous resets (better timing)
- Parameterize for reusability
- Consider retiming opportunities

**Example of retiming-friendly code:**
```systemverilog
// Pipeline registers for high-speed
logic [31:0] stage1, stage2;

always_ff @(posedge clk) begin
    stage1 <= input_data + 32'd5;
    stage2 <= stage1 * 32'd3;
    output_data <= stage2 - 32'd7;
end
```

### Timing Closure

- **Setup time**: Data must be stable before clock edge
- **Hold time**: Data must remain stable after clock edge
- **Clock-to-Q**: FF propagation delay
- **Critical path**: Longest combinational path

**Path equation:**
```
T_clk >= T_cq + T_comb + T_setup + T_skew
```

---

## Design Guidelines

### Coding Style

✅ **DO:**
```systemverilog
// Good: Clear, parameterized, synchronous reset
module good_counter #(parameter WIDTH = 8) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             en,
    output logic [WIDTH-1:0] count
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= '0;
        else if (en)
            count <= count + 1;
    end
endmodule
```

❌ **DON'T:**
```systemverilog
// Bad: Hardcoded width, async reset in sync process, no enable
module bad_counter (
    input  wire       clk, rst,
    output reg [7:0]  count
);
    always @(posedge clk) begin
        if (rst == 1'b1)  // Async reset in sync process!
            count = 8'h0;
        else
            count = count + 1;
    end
endmodule
```

### Parameterization Best Practices

```systemverilog
module parameterized_module #(
    parameter WIDTH = 32,
    parameter DEPTH = 16,
    parameter type DATA_TYPE = logic [WIDTH-1:0],
    
    // Derived parameters
    localparam ADDR_WIDTH = $clog2(DEPTH)
) (
    // ...
);
```

### Reset Strategy

**Synchronous Reset (Recommended):**
- Better timing (reset is just another data path)
- Works with clock gating
- Standard in most designs

**Asynchronous Reset:**
- Faster reset response
- Required for some applications (safety-critical)
- More complex timing analysis

### CDC Best Practices

1. **Never cross multiple bits without synchronization**
2. **Use gray code for multi-bit counters**
3. **Handshake for multi-bit data**
4. **FIFO for high-throughput**
5. **Formal verification for CDC**

---

## Testing Strategy

### Verification Approach

For each block, create:

1. **Direct RTL testbench**
   - Basic functionality
   - Corner cases
   - Protocol compliance

2. **UVM testbench** (see 05_verification)
   - Constrained random
   - Functional coverage
   - Reference model

3. **Assertions**
   - Protocol checks
   - Data integrity
   - No overflow/underflow

### Example Test Plan (FIFO)

| Test Case | Description | Coverage |
|-----------|-------------|----------|
| Basic write/read | Simple push/pop | Sanity |
| Fill and drain | Write until full, read until empty | Full/empty flags |
| Simultaneous | Write and read same cycle | Count logic |
| Back-to-back | Continuous operation | Throughput |
| Random | Random write/read timing | Corner cases |
| Almost flags | Check almost_full/empty | Status flags |

### Assertions for FIFO

```systemverilog
// No overflow
property no_overflow;
    @(posedge clk) disable iff (!rst_n)
    full |-> !wr_en;
endproperty
assert property (no_overflow);

// No underflow
property no_underflow;
    @(posedge clk) disable iff (!rst_n)
    empty |-> !rd_en;
endproperty
assert property (no_underflow);

// Count matches full/empty
property count_valid;
    @(posedge clk) disable iff (!rst_n)
    (count == 0) == empty && (count == DEPTH) == full;
endproperty
assert property (count_valid);
```

---

## Learning Path

### Beginner (Week 1-2)
1. **Start simple**: Edge detectors, pulse generators
2. **Counters**: Binary, gray code
3. **Basic mux/decoder**: 2:1, 4:1 mux
4. **Synchronizer**: Two-flop sync

### Intermediate (Week 3-4)
5. **FIFO**: Synchronous FIFO with testbench
6. **Arbiter**: Fixed priority, round-robin
7. **Width converter**: Upsizer/downsizer
8. **CRC**: CRC-8 implementation

### Advanced (Week 5-8)
9. **Async FIFO**: Full CDC-safe implementation
10. **Advanced arbiter**: Weighted round-robin
11. **Hamming code**: SECDED implementation
12. **LFSR**: Multiple polynomials, parallel

### Expert (Ongoing)
13. **Optimize**: Area, timing, power
14. **Verify**: Formal verification
15. **Reuse**: Generic, configurable libraries
16. **Integration**: Use in larger designs

---

## Implementation Checklist

For each block:

- [ ] **Specification**
  - [ ] Clear interface definition
  - [ ] Parameter documentation
  - [ ] Timing diagrams
  
- [ ] **RTL Implementation**
  - [ ] Parameterized
  - [ ] Synthesis-friendly
  - [ ] Reset strategy defined
  - [ ] CDC-safe (if applicable)
  
- [ ] **Verification**
  - [ ] Testbench with directed tests
  - [ ] Corner case coverage
  - [ ] Assertions for protocol
  - [ ] Waveform review
  
- [ ] **Documentation**
  - [ ] README with usage example
  - [ ] Parameter descriptions
  - [ ] Known limitations
  - [ ] Synthesis results (optional)

---

## Common Pitfalls

### 1. FIFO Pitfalls
- **Wrong full/empty logic**: Off-by-one errors
- **Simultaneous read/write**: Not handling correctly
- **Async FIFO metastability**: Missing synchronizers

### 2. CDC Pitfalls
- **Multiple bits**: Crossing without gray code/handshake
- **No synchronizer**: Direct clock domain crossing
- **Combinational logic**: Between domains

### 3. Arbiter Pitfalls
- **Starvation**: Low priority never granted
- **Combinational loops**: In grant logic
- **Glitches**: In grant signals

### 4. Synthesis Pitfalls
- **Inferred latches**: Incomplete case/if statements
- **Combinational loops**: Unintended feedback
- **Non-synthesizable constructs**: Delays, initial blocks

---

## Tools and Simulation

### Simulation
```bash
# Using ModelSim/Questa
vlog -sv module.sv testbench.sv
vsim -c testbench -do "run -all; quit"

# Using VCS
vcs -sverilog module.sv testbench.sv
./simv

# Using Verilator (open-source)
verilator --cc module.sv --exe testbench.cpp
make -C obj_dir -f Vmodule.mk
./obj_dir/Vmodule
```

### Synthesis
```bash
# Using Synopsys Design Compiler
dc_shell -f synthesis_script.tcl

# Using Yosys (open-source)
yosys -p "read_verilog module.sv; synth; write_verilog synth.v"
```

### Waveform Viewing
- **ModelSim/Questa**: Use wave.do scripts
- **Verdi**: Advanced debug features
- **GTKWave**: Open-source viewer

---

## Real-World Applications

### Where These Blocks Are Used

| Block | Application Examples |
|-------|---------------------|
| **Arbiters** | Bus arbitration, memory controllers, NoC routers |
| **FIFOs** | Video pipelines, network buffers, protocol converters |
| **Synchronizers** | Multi-clock SoCs, FPGA designs, async interfaces |
| **CRC** | Ethernet, USB, SD cards, Flash memory |
| **LFSR** | Test pattern generation, scrambling, PRNG |
| **Width Converters** | Memory interfaces, protocol bridges, DMA |

### Industry Examples

1. **Ethernet MAC**: Uses CRC-32, async FIFOs, arbiters
2. **DDR Controller**: Width converters, sophisticated arbitration
3. **USB Controller**: CRC-5/CRC-16, CDC synchronizers
4. **Video Pipeline**: FIFOs everywhere, width conversion
5. **Network Router**: Complex arbitration, deep FIFOs

---

## References

### Books
- "Digital Design and Computer Architecture" - Harris & Harris
- "RTL Modeling with SystemVerilog for Simulation and Synthesis" - Sutherland
- "Advanced Chip Design" - Sangiovanni-Vincentelli
- "FPGA Prototyping by SystemVerilog Examples" - Chu

### Papers
- "Simulation and Synthesis Techniques for Asynchronous FIFO Design" - Clifford Cummings
- "Clock Domain Crossing (CDC) Design & Verification Techniques" - Cummings
- "Arbiters: Design Ideas and Coding Styles" - Matt Weber

### Standards
- IEEE 1364: Verilog HDL
- IEEE 1800: SystemVerilog
- IEEE 1801: UPF (for low power)

### Online Resources
- ASIC World (http://www.asic-world.com)
- FPGA4Fun (https://www.fpga4fun.com)
- ZipCPU Blog (https://zipcpu.com)
- Project F (https://projectf.io)

### Open-Source Libraries
- OpenCores (https://opencores.org)
- LibreCores (https://www.librecores.org)
- PULP Platform (https://pulp-platform.org)
- Enjoy-Digital LiteX

---

## Performance Metrics

### Benchmarking

Track these metrics for each implementation:

| Metric | Description | Typical Values |
|--------|-------------|----------------|
| **Area** | Logic cells / gates | Varies by block |
| **f_max** | Maximum frequency | >100 MHz typical |
| **Latency** | Input to output delay | 1-10 cycles |
| **Throughput** | Data per cycle | Depends on design |
| **Power** | Dynamic + static | Use power estimation tools |

### Example Synthesis Results (FIFO)

```
FIFO Depth=16, Width=32, sync_fifo.sv
Technology: Generic 28nm
Area: 450 gates (estimate)
f_max: 250 MHz
Latency: 1 cycle (registered output)
Power: 2.5 mW @ 100MHz, 0.5V
```

---

## Contributing

When adding new blocks:

1. **Follow naming convention**: `block_name.sv`
2. **Include testbench**: `block_name_tb.sv`
3. **Add README**: Explain purpose, parameters, usage
4. **Document parameters**: Clear descriptions
5. **Add assertions**: Protocol and data checks
6. **Show waveforms**: Key scenarios
7. **Synthesis notes**: If applicable

---

## Quick Reference: Common Patterns

### Always Block Patterns

```systemverilog
// Clocked with async reset
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        // reset
    else
        // logic
end

// Clocked with sync reset
always_ff @(posedge clk) begin
    if (!rst_n)
        // reset
    else
        // logic
end

// Combinational
always_comb begin
    // logic
end
```

### Handshake Pattern

```systemverilog
// Source
output logic valid;
input  logic ready;
output logic [WIDTH-1:0] data;

// Valid-ready handshake
// Transfer occurs when valid && ready

// Sink
input  logic valid;
output logic ready;
input  logic [WIDTH-1:0] data;
```

---

**Last Updated**: January 2026
**Maintainer**: System Verilog Workshop
