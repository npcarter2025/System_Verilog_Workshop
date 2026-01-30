
TEST ?= $(wildcard *.sv)
# dynamic_arrays.sv


all: compile run log

compile:
	vcs -sverilog -debug_access+all -full64 +v2k -timescale=1ns/1ps -o simv $(TEST)

run:
	./simv

log:
	./simv -l sim.log

clean:
	rm -rf simv *.key *.daidir csrc *.log

.PHONY: compile run log clean