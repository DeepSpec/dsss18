coq: Makefile.coq $(EXTR_BIN)
	@$(MAKE) -f $<

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean:
	# TODO
