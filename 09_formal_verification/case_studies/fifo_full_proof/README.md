# FIFO Complete Formal Proof

This case study demonstrates a **complete formal verification** of a synchronous FIFO, proving correctness using SystemVerilog Assertions and formal tools.

## Files

- **`fifo_model.sv`** - The FIFO design (DUT - Design Under Test)
- **`fifo_properties.sv`** - Comprehensive formal properties
- **`formal_tb.sv`** - Formal testbench binding DUT and properties

## What's Being Proven

### 1. Safety Properties ✓
- **No overflow**: Cannot push when full
- **No underflow**: Cannot pop when empty
- **Mutual exclusion**: Not both full and empty (unless DEPTH=1)

### 2. Flag Correctness ✓
- `empty` flag matches `count == 0`
- `full` flag matches `count == DEPTH`
- `almost_empty` flag matches `count == 1`
- `almost_full` flag matches `count == DEPTH-1`
- Count always within valid range [0, DEPTH]

### 3. Count Operations ✓
- Push increments count (when not full and not popping)
- Pop decrements count (when not empty and not pushing)
- Simultaneous push/pop keeps count stable
- Count stable when no operations

### 4. Data Integrity ✓
- **Critical**: Data read matches data written
- Uses shadow memory to track expected vs actual
- Proves FIFO ordering (first-in-first-out)

### 5. Reset Behavior ✓
- FIFO empty after reset
- FIFO not full after reset
- All internal state cleared

## How to Run

### Using JasperGold (Cadence)

```tcl
# Load design
clear -all
analyze -sv09 fifo_model.sv fifo_properties.sv formal_tb.sv
elaborate -top fifo_formal_tb

# Configure formal
clock aclk
reset -expression {!aresetn}
set_prove_time_limit 3600
set_max_trace_length 50

# Run verification
prove -all

# Check coverage
prove -cover -all

# Generate report
report
```

### Using VC Formal (Synopsys)

```tcl
# Setup
set_formal_mode setup
read_file -format sverilog fifo_model.sv
read_file -format sverilog fifo_properties.sv  
read_file -format sverilog formal_tb.sv

# Elaborate
elaborate fifo_formal_tb

# Configure
clock clk
reset -expression (!rst_n)

# Prove
set_formal_property_depth 50
prove -all
```

### Using SymbiYosys (Open-Source)

Create `fifo_formal.sby`:

```ini
[tasks]
prove
cover

[options]
prove: mode prove
prove: depth 40
cover: mode cover
cover: depth 20

[engines]
smtbmc z3

[script]
read -formal fifo_model.sv
read -formal fifo_properties.sv
read -formal formal_tb.sv
prep -top fifo_formal_tb

[files]
fifo_model.sv
fifo_properties.sv
formal_tb.sv
```

Run:
```bash
sby fifo_formal.sby
```

## Expected Results

### All Assertions Should PROVE ✓

```
✓ a_no_overflow          - Proven
✓ a_no_underflow         - Proven
✓ a_mutex                - Proven
✓ a_count_empty          - Proven
✓ a_count_full           - Proven
✓ a_almost_empty         - Proven
✓ a_almost_full          - Proven
✓ a_count_range          - Proven
✓ a_push_incr            - Proven
✓ a_pop_decr             - Proven
✓ a_simul_stable         - Proven
✓ a_count_stable         - Proven
✓ a_data_match           - Proven (critical!)
✓ a_shadow_match         - Proven
✓ a_reset_empty          - Proven
✓ a_reset_not_full       - Proven
```

### All Covers Should Be Reachable ✓

```
✓ c_full                 - Reachable
✓ c_full_to_empty        - Reachable
✓ c_consec_push          - Reachable
✓ c_consec_pop           - Reachable
✓ c_simul                - Reachable
✓ c_push_almost_full     - Reachable
✓ c_pop_almost_empty     - Reachable
✓ c_fill                 - Reachable
✓ c_drain                - Reachable
```

## Proof Depth

For FIFO with DEPTH=16:
- **Minimum depth**: 20 cycles (to fill FIFO)
- **Recommended**: 40-50 cycles (to fill and drain)
- **Why**: Need to exercise full cycle of operations

Smaller depth (e.g., 4) proves faster - good for initial verification.

## Understanding Results

### If Assertion FAILS

The formal tool will provide a **counterexample**:
- Exact sequence of `push`, `pop`, `wr_data` inputs
- Cycle-by-cycle waveform showing the bug
- Shows when assertion triggered

**Example counterexample**:
```
Cycle 0: rst_n=0
Cycle 1: rst_n=1, push=1, wr_data=0xAA
Cycle 2: push=1, wr_data=0xBB
...
Cycle 10: pop=1 -> rd_data=0xCC (expected 0xAA!) <- BUG
```

### If Cover is UNREACHABLE

Possible reasons:
1. **Over-constrained**: Assumptions too strict
2. **Insufficient depth**: Need more cycles
3. **Actual limitation**: Design can't reach that state

## Common Bugs Found by Formal

1. **Off-by-one errors**: 
   - Wrong full/empty condition
   - `count == DEPTH` vs `count == DEPTH-1`

2. **Simultaneous operation bugs**:
   - Push and pop same cycle
   - Wrong count update

3. **Pointer wraparound**:
   - Incorrect modulo arithmetic
   - Extra bit forgotten

4. **Data integrity**:
   - Wrong read address
   - Overwriting data

## Debugging Tips

1. **Start small**: Use DEPTH=4 for fast iteration
2. **One property at a time**: Comment out others initially
3. **Use covers**: Verify properties are exercised
4. **Check assumptions**: Make sure environment is reasonable
5. **View waveforms**: Counterexamples show exact bug

## Advanced Topics

### Parametric Verification

Prove for multiple DEPTH values:
```systemverilog
// In formal script
for (int d = 4; d <= 64; d *= 2) begin
    set_parameter DEPTH d
    prove -all
end
```

### Assume-Guarantee Reasoning

Add assumptions for well-behaved environment:
```systemverilog
assume property (@(posedge clk)
    full |-> !push);  // Don't push when full

assume property (@(posedge clk)
    empty |-> !pop);  // Don't pop when empty
```

Then assertions prove with these constraints.

### Data Integrity Proof

The shadow memory technique:
1. Create parallel array tracking writes
2. Compare reads against shadow
3. Proves no data corruption or misordering

This is the **gold standard** for FIFO verification!

## Comparison: Simulation vs Formal

| Aspect | Simulation | Formal |
|--------|-----------|--------|
| **Coverage** | Random tests | Exhaustive |
| **Time** | Fast | Slower |
| **Confidence** | Statistical | Mathematical proof |
| **Bug Finding** | Might miss corner cases | Finds all bugs in scope |
| **Depth** | Unlimited | Bounded (but usually sufficient) |

**Best Practice**: Use both!
- Formal for protocol and corner cases
- Simulation for overall system integration

## Success Criteria

For production FIFO:
- ✓ All assertions prove
- ✓ All covers reachable
- ✓ Depth sufficient (2*DEPTH minimum)
- ✓ Multiple DEPTH values tested (4, 8, 16, 32)
- ✓ No assumption violations
- ✓ Counterexamples reviewed and fixed

## Learning Outcomes

After completing this case study, you'll understand:
1. How to write comprehensive formal properties
2. Safety vs liveness properties
3. Data integrity verification techniques
4. Shadow memory method
5. Formal tool usage
6. How to debug counterexamples

---

**Next Steps**: Try modifying the FIFO and see if formal catches your bugs!
- Change `count == DEPTH` to `count == DEPTH+1` (should fail)
- Remove pointer increment (should fail data integrity)
- Break flag logic (should fail flag properties)

Formal verification will immediately show you the bug!
