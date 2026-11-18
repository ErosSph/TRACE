# Build the TRACE Coq framework (semantics, ISA specification, shared proof library).
# Needs the dep/ submodules built first (see the top-level Makefile).
.PHONY: all clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

clean:
	if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d
