TEST ?= $(wildcard *.sv)
VCS = vcs
BUILD_DIR = build
SIMV = $(BUILD_DIR)/simv
 
TB_TOP ?=

TOP_FLAG = $(if $(TB_TOP), -top $(TB_TOP),)

SIM_FLAGS = -sverilog $(TOP_FLAG) -debug_access+all -full64 +v2k -timescale=1ns/1ps -Mdir=$(BUILD_DIR)/csrc

all: compile run

compile: $(BUILD_DIR)
	$(VCS) $(SIM_FLAGS) -o $(SIMV) $(TEST)

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

run: compile
	./$(SIMV)

log: compile
	./$(SIMV) | tee $(BUILD_DIR)/sim.log

clean:
	rm -rf $(BUILD_DIR) *.daidir *.log *.key csrc simv


.PHONY: all compile run log clean help 