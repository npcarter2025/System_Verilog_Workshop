# SystemVerilog Simulator Guide

This document describes the available simulators on this machine and how to use them.

---

## Available Simulators

### 1. VCS (Synopsys)

**Status**: ✅ Installed and available in PATH

**Installation Details**:
- **Location**: `/share/instsww/synopsys-new/vcs/T-2022.06-SP2-9/`
- **Version**: VCS T-2022.06-SP2-9
- **Already in PATH**: Yes

**How to Call**:
```bash
vcs [options] <source_files>
```

**Common VCS Flags**:

| Flag | Description |
|------|-------------|
| `-sverilog` | Enable SystemVerilog support |
| `-ntb_opts uvm-1.2` | Enable UVM 1.2 support |
| `-full64` | Compile for 64-bit mode |
| `-timescale=1ns/1ps` | Set time unit and precision |
| `+acc` | Enable code coverage and debugging |
| `+vpi` | Enable VPI (Verilog Procedural Interface) |
| `-debug_access+all` | Enable full debug access |
| `-R` | Compile and run immediately |
| `-l <logfile>` | Specify log file name |
| `+incdir+<dir>` | Add include directory |
| `-f <file.f>` | Read file list from file |
| `-v <lib.v>` | Specify library file |
| `-y <dir>` | Library directory search path |
| `+libext+.v+.sv` | Library file extensions |
| `-CFLAGS <flags>` | Pass flags to C compiler |
| `-cm line+cond+fsm+tgl+branch` | Enable code coverage |
| `-cm_name <name>` | Name for coverage database |
| `-lca` | Enable line coverage |

**UVM-Specific Flags**:
```bash
+UVM_TESTNAME=<test_name>      # Specify test to run
+UVM_VERBOSITY=<level>         # UVM_NONE, UVM_LOW, UVM_MEDIUM, UVM_HIGH, UVM_FULL, UVM_DEBUG
+UVM_PHASE_TRACE               # Enable phase tracing
+UVM_OBJECTION_TRACE           # Enable objection tracing
+UVM_CONFIG_DB_TRACE           # Trace config DB operations
+UVM_TIMEOUT=<value>           # Set simulation timeout
```

**Example Compilation**:
```bash
# Basic compilation with UVM
vcs -sverilog -full64 -ntb_opts uvm-1.2 \
    -timescale=1ns/1ps +acc +vpi \
    +incdir+../tb/include \
    -f ../dut/files.f \
    ../tb/top_pkg.sv \
    ../tb/top_tb.sv

# Compile and run
vcs -sverilog -ntb_opts uvm-1.2 -R \
    +UVM_TESTNAME=my_test \
    +UVM_VERBOSITY=UVM_MEDIUM \
    source_files.sv

# With code coverage
vcs -sverilog -ntb_opts uvm-1.2 \
    -cm line+cond+fsm+tgl \
    -cm_name my_test_cov \
    -debug_access+all \
    source_files.sv
```

**Running Simulation**:
```bash
# After compilation
./simv

# With runtime options
./simv +UVM_TESTNAME=my_test +UVM_VERBOSITY=UVM_HIGH

# With waveform dumping (if compiled with -debug_access)
./simv -gui &
```

**Waveform Viewing**:
```bash
# Using Verdi (if available)
verdi -ssf <waveform.fsdb> &

# Using DVE
dve -full64 -vpd <waveform.vpd> &
```

---

### 2. Questa/ModelSim (Mentor Graphics)

**Status**: ✅ Installed and licensed

**Installation Details**:
- **Location**: `/share/instsww/mgc/questasim/`
- **Version**: Questa Sim-64 vsim 10.7c_4 (2019.02)
- **UVM Support**: UVM 1.2 included
- **License Server**: `1717@license-srv.eecs.berkeley.edu`

**How to Add to PATH**:
```bash
export PATH=/share/instsww/mgc/questasim/bin:$PATH
```

**How to Call**:
```bash
# Compile Verilog/SystemVerilog
vlog [options] <source_files>

# Compile VHDL
vcom [options] <source_files>

# Run simulation
vsim [options] <top_module>
```

**Common Questa Flags**:

**vlog (Compiler) Flags**:

| Flag | Description |
|------|-------------|
| `-sv` | Enable SystemVerilog support |
| `+acc` | Enable debug/coverage access |
| `-timescale=1ns/1ps` | Set time unit and precision |
| `-work <lib>` | Specify work library (default: work) |
| `-l <logfile>` | Specify log file |
| `+incdir+<dir>` | Add include directory |
| `-f <file.f>` | Read file list from file |
| `-suppress <msg>` | Suppress warning/error messages |
| `-hazards` | Enable hazard detection |
| `-lint` | Enable lint checking |
| `+cover` | Enable code coverage |
| `-writetoplevels <file>` | Write top-level modules to file |
| `+define+<macro>` | Define preprocessor macro |

**vsim (Simulator) Flags**:

| Flag | Description |
|------|-------------|
| `-c` | Command-line mode (no GUI) |
| `-gui` | GUI mode |
| `-do <script.do>` | Execute Tcl/DO script |
| `-l <logfile>` | Specify log file |
| `-wlf <waveform.wlf>` | Specify waveform file |
| `-novopt` | Disable optimization (for debugging) |
| `-voptargs=+acc` | Enable debug access with optimization |
| `+UVM_TESTNAME=<test>` | Specify UVM test |
| `+UVM_VERBOSITY=<level>` | Set UVM verbosity |
| `-coverage` | Enable coverage collection |
| `-sv_seed <value>` | Set random seed |
| `-onfinish stop` | Stop simulation at end (don't exit) |
| `-onfinish exit` | Exit at end of simulation |

**UVM-Specific Flags** (same as VCS):
```bash
+UVM_TESTNAME=<test_name>
+UVM_VERBOSITY=UVM_LOW|UVM_MEDIUM|UVM_HIGH|UVM_FULL
+UVM_PHASE_TRACE
+UVM_OBJECTION_TRACE
+UVM_CONFIG_DB_TRACE
+UVM_TIMEOUT=<value>,<override>
```

**Example Compilation**:
```bash
# Create work library
vlib work

# Compile with UVM
vlog -sv +acc \
     +incdir+../tb/include \
     -f ../dut/files.f \
     ../tb/top_pkg.sv \
     ../tb/top_tb.sv

# Compile with UVM library path explicitly
vlog -sv +acc \
     +incdir+$QUESTA_HOME/verilog_src/uvm-1.2/src \
     +incdir+../tb/include \
     source_files.sv
```

**Running Simulation**:
```bash
# Command-line mode
vsim -c -do "run -all; quit" top_tb

# With UVM test
vsim -c -do "run -all; quit" \
     +UVM_TESTNAME=my_test \
     +UVM_VERBOSITY=UVM_MEDIUM \
     top_tb

# GUI mode with waveforms
vsim -gui top_tb

# GUI mode with automatic waveform logging
vsim -gui -do "log -r /*; run -all" top_tb

# With coverage
vsim -coverage -c -do "run -all; quit" top_tb
```

**Interactive Simulation (in vsim console)**:
```tcl
# Add waves
add wave -r /*
add wave sim:/top_tb/*

# Run simulation
run 100ns
run -all

# Restart simulation
restart -force

# Quit
quit
```

**Batch Mode with DO Script**:
```bash
# Create a run.do script:
# run.do:
# ---
# vlib work
# vlog -sv +acc source.sv
# vsim -c top_tb
# add wave -r /*
# run -all
# quit

# Execute it:
vsim -c -do run.do
```

---

## License Configuration

### Environment Variables

```bash
# FlexLM License (used by VCS, Questa, and others)
LM_LICENSE_FILE=5280@license-srv.eecs.berkeley.edu:2100@license-srv.eecs.berkeley.edu:1717@license-srv.eecs.berkeley.edu

# Mentor Graphics specific
MGLS_LICENSE_FILE=1717@license-srv.eecs.berkeley.edu
```

### Check License Status

**For VCS**:
```bash
vcs -ID
```

**For Questa**:
```bash
vsim -version
vlog -version
```

**Check FlexLM License Server**:
```bash
# If lmstat is available
lmstat -a -c $LM_LICENSE_FILE
```

---

## Comparison: VCS vs Questa

| Feature | VCS | Questa |
|---------|-----|--------|
| **Performance** | Very fast | Fast |
| **Memory Usage** | Lower | Moderate |
| **GUI** | DVE/Verdi | QuestaSim GUI |
| **Waveform Format** | VPD/FSDB | WLF |
| **Debug Features** | Excellent | Excellent |
| **UVM Support** | UVM 1.2 | UVM 1.2 |
| **Industry Use** | Very common | Very common |
| **Learning Curve** | Moderate | Easy |

---

## Quick Reference Card

### VCS Workflow
```bash
# 1. Compile
vcs -sverilog -ntb_opts uvm-1.2 -full64 \
    +incdir+inc -f files.f top.sv

# 2. Run
./simv +UVM_TESTNAME=test +UVM_VERBOSITY=UVM_MEDIUM

# 3. View waves (if compiled with -debug_access+all)
verdi -ssf waves.fsdb &
```

### Questa Workflow
```bash
# 1. Setup
vlib work

# 2. Compile
vlog -sv +acc +incdir+inc -f files.f top.sv

# 3. Run
vsim -c -do "run -all; quit" +UVM_TESTNAME=test top_tb

# 4. View waves (GUI)
vsim -gui top_tb
```

---

## Tips and Best Practices

### 1. **Use File Lists** (`files.f`)
Instead of listing all files on command line:
```bash
vcs -f compile.f
vlog -f compile.f
```

### 2. **Enable Code Coverage**
```bash
# VCS
vcs -cm line+cond+fsm+tgl -cm_name test_cov ...

# Questa
vlog +cover ...
vsim -coverage ...
```

### 3. **Random Seed Control**
```bash
# VCS
./simv +ntb_random_seed=12345

# Questa
vsim -sv_seed 12345 ...
```

### 4. **Dump Waveforms**
```systemverilog
// In your testbench
initial begin
  $fsdbDumpfile("waves.fsdb");  // VCS/Verdi
  $fsdbDumpvars(0, top_tb);
  
  // OR for VCD (universal)
  $dumpfile("waves.vcd");
  $dumpvars(0, top_tb);
end
```

### 5. **Suppress Common Warnings**
```bash
# VCS
vcs -suppress=<msg_id> ...

# Questa
vlog -suppress <msg_id> ...
```

### 6. **Parallel Compilation** (for large projects)
```bash
# VCS
vcs -j8 ...  # Use 8 parallel jobs

# Questa
vlog -j 8 ... # Use 8 parallel jobs
```

---

## Troubleshooting

### Issue: "License not found"
**Solution**: Check environment variables
```bash
echo $LM_LICENSE_FILE
echo $MGLS_LICENSE_FILE
```

### Issue: "UVM package not found"
**Solution**: Use `-ntb_opts uvm-1.2` (VCS) or ensure Questa's UVM is in path

### Issue: "Module not found"
**Solution**: Check include directories with `+incdir+<path>`

### Issue: "Simulation hangs"
**Solution**: Add timeout
```bash
+UVM_TIMEOUT=10000,NO  # 10000 time units
```

---

## Additional Resources

- VCS User Guide: `/share/instsww/synopsys-new/vcs/T-2022.06-SP2-9/doc/`
- Questa User Manual: `/share/instsww/mgc/questasim/docs/`
- UVM 1.2 Class Reference: Available in simulator installations

---

**Generated**: 2026-02-06  
**Machine**: EECS Berkeley cluster
