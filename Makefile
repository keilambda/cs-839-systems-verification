.PHONY: all clean

-include .Makefile.coq.d

all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
