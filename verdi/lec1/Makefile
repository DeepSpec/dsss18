VS:=$(wildcard SimpleDS/*.v)

ARGS := \
	-Q StructTact StructTact \
	-R SimpleDS SimpleDS

.PHONY: coq
coq: Makefile.coq
	$(MAKE) -C StructTact
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	$(COQBIN)coq_makefile $(ARGS) $(VS) -o Makefile.coq

.PHONY: clean
clean: Makefile.coq
	$(MAKE) -C StructTact clean
	$(MAKE) -f Makefile.coq clean
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f Makefile.coq Makefile.coq.conf .coqdeps.d
