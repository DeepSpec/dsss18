.PHONY: coq
coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: clean
clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f Makefile.coq Makefile.coq.conf .coqdeps.d
