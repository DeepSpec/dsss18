SERVER = out/dw-swap-server
EXCLUDE= Proofs Spec/TopLevelSpec.v Spec/Vst Spec/main.v \
		 Lib/VstLib.v docs \
         Spec/Swap_SimpleSpec_Examples.v
OCAMLBUILDFLAGS=-libs unix,str
QC = quickChick -color -top "" -ocamlbuild '$(OCAMLBUILDFLAGS)' \
	 -cmd '$(MAKE) coq-qc' $(QCFLAGS)
CFLAGS=-DBUFFER_SIZE=3
V=@

coq: Makefile.coq $(EXTR_BIN)
	$V$(MAKE) -f $<

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@ 2>> /tmp/client_error

build-with-vst:
	make -f Makefile.vst build VERBOSE=true

test:
	$V$(MAKE) 
	@echo
	@echo ------------------- Internal tests ----------------------
	$V$(MAKE) testcoq
	@echo
	@echo ------------------- Examples ----------------------
	$V$(MAKE) testcoq-examples
	@echo
	@echo ------------------- External tests ----------------------
	$V$(MAKE) testexternal --quiet

testcoq:
	$V$(QC) -s CLikeTest -exclude $(EXCLUDE)

testcoq-examples:
	$V$(QC) -s SwapExamples -N 100 -exclude $(EXCLUDE)

testexternal: $(SERVER)
	$V$(RM) /tmp/server_log /tmp/client_log /tmp/server_error /tmp/client_error
	$V$(QC) -s ExternalTest -N 100 -exclude $(EXCLUDE)

$(SERVER): DeepWeb/Spec/main.c DeepWeb/Spec/macros.h
	$Vmkdir -p out/
	$V$(CC) $(CFLAGS) -IDeepWeb/Spec/ $< -o $@

server: $(SERVER) stop
	$Vexec $< &

stop:
	$Vif [ -n "$$(pgrep "$(notdir $(SERVER))")" ]; then pkill "$(notdir $(SERVER))"; fi

coq-qc: $(SERVER)
	$Vperl -i -p0e 's/^(Separate Extraction)(\s+\S+)*?((\s+test\S+)*)\s*\.$$/\1\3./m' QuickChickTop.v
	$Vecho "-Q . ''" > _CoqProject.tmp
	$Vcat _CoqProject >> _CoqProject.tmp
	$Vcoq_makefile -f _CoqProject.tmp -o Makefile.tmp 2>> /tmp/client_error
	$Vmake -f Makefile.tmp QuickChickTop.vo
	$Vecho 'let _ = print_endline "done"' >> QuickChickTop.ml

docs: build-with-vst
	$(MAKE) -f Makefile.coq.vst html VERBOSE=true
	rm -rf docs
	mv html docs

clean:
	find . -name "*.vo" -print -exec rm -rf {} \;
	find . -name "*.glob" -print -exec rm -rf {} \;
	find . -name ".*.aux" -print -exec rm -rf {} \;
	-$(MAKE) -f Makefile.coq clean
	-rm -rf ../_qc_dw.tmp html Makefile.coq* _CoqProject.Vst .coqdeps.d

.PHONY: docs clean coq-qc test coq

# Just for BCP
bcp:
	$(MAKE) -C $(HOME)/dw/src dsss18 -j
	$(MAKE) -j docs COQDOCFLAGS="-interpolate -utf8 --parse-comments"
	osascript $(HOME)/s/tools/safari-reload.as
	$(MAKE) -j test
