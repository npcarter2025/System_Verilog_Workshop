#!/bin/bash
# ============================================================================
# run.sh - Script to compile and run UVM Hello World example
# ============================================================================

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "========================================="
echo "UVM Hello World - Compilation & Execution"
echo "========================================="

# Check for simulator
if command -v vlog &> /dev/null; then
    SIMULATOR="questa"
    echo -e "${GREEN}Detected: QuestaSim/ModelSim${NC}"
elif command -v vcs &> /dev/null; then
    SIMULATOR="vcs"
    echo -e "${GREEN}Detected: VCS${NC}"
elif command -v xvlog &> /dev/null; then
    SIMULATOR="xcelium"
    echo -e "${GREEN}Detected: Xcelium${NC}"
else
    echo -e "${RED}Error: No supported simulator found!${NC}"
    echo "Supported simulators: QuestaSim, VCS, Xcelium"
    exit 1
fi

# Clean previous compilation
echo ""
echo "Cleaning previous compilation..."
rm -rf work *.log transcript simv* csrc DVEfiles *.key *.vpd xcelium.d

# Compile and run based on simulator
case $SIMULATOR in
    questa)
        echo ""
        echo "========================================="
        echo "Compiling with QuestaSim..."
        echo "========================================="
        
        # Create work library
        vlib work
        
        # Compile UVM package
        vlog -sv +incdir+$UVM_HOME/src $UVM_HOME/src/uvm_pkg.sv
        
        # Compile design
        vlog -sv hello_uvm.sv
        
        if [ $? -eq 0 ]; then
            echo -e "${GREEN}Compilation successful!${NC}"
            
            echo ""
            echo "========================================="
            echo "Running simulation..."
            echo "========================================="
            
            # Run simulation
            vsim -c top -do "run -all; quit" +UVM_VERBOSITY=UVM_LOW
            
            if [ $? -eq 0 ]; then
                echo -e "${GREEN}Simulation completed successfully!${NC}"
            else
                echo -e "${RED}Simulation failed!${NC}"
                exit 1
            fi
        else
            echo -e "${RED}Compilation failed!${NC}"
            exit 1
        fi
        ;;
        
    vcs)
        echo ""
        echo "========================================="
        echo "Compiling with VCS..."
        echo "========================================="
        
        # Compile and elaborate
        vcs -sverilog -ntb_opts uvm-1.2 -full64 hello_uvm.sv -l compile.log
        
        if [ $? -eq 0 ]; then
            echo -e "${GREEN}Compilation successful!${NC}"
            
            echo ""
            echo "========================================="
            echo "Running simulation..."
            echo "========================================="
            
            # Run simulation
            ./simv +UVM_VERBOSITY=UVM_LOW -l sim.log
            
            if [ $? -eq 0 ]; then
                echo -e "${GREEN}Simulation completed successfully!${NC}"
            else
                echo -e "${RED}Simulation failed!${NC}"
                exit 1
            fi
        else
            echo -e "${RED}Compilation failed!${NC}"
            exit 1
        fi
        ;;
        
    xcelium)
        echo ""
        echo "========================================="
        echo "Compiling with Xcelium..."
        echo "========================================="
        
        # Compile and run
        xrun -uvm -sv hello_uvm.sv +UVM_VERBOSITY=UVM_LOW -l xrun.log
        
        if [ $? -eq 0 ]; then
            echo -e "${GREEN}Compilation and simulation successful!${NC}"
        else
            echo -e "${RED}Failed!${NC}"
            exit 1
        fi
        ;;
esac

echo ""
echo "========================================="
echo "Done!"
echo "========================================="
