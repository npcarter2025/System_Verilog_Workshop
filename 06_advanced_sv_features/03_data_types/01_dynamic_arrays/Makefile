
TEST ?= $(wildcard *.sv)
# dynamic_arrays.sv

TB_TOP ?=
TOP_FLAG = $(if $(TB_TOP), -top $(TB_TOP),)


all: compile run log

compile:
	vcs -sverilog $(TOP_FLAG) -debug_access+all -full64 +v2k -timescale=1ns/1ps -o simv $(TEST)

run:
	./simv

log:
	./simv -l sim.log

clean:
	rm -rf simv *.key *.daidir csrc

.PHONY: compile run log clean