# Top-level build: Coq dependencies, then the TRACE framework (src/).
.PHONY: all deps clean

all: deps
	$(MAKE) -C src

deps:
	$(MAKE) -C dep/coqutil
	$(MAKE) -C dep/riscv-coq


clean:
	$(MAKE) -C src clean
