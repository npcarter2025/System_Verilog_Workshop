
TEST ?= $(wildcard *.sv)
# dynamic_arrays.sv


all: compile

compile:
	vcs -sverilog -debug_access+all -full64 +v2k -timescale=1ns/1ps -o simv $(TEST)

run:
	./simv

log:
	./simv -l sim.log

clean:
	rm -rf simv *.key *.daidir csrc

.PHONY: compile run log clean