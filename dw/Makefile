SERVER = out/dw-swap-server
EXCLUDE= Proofs Spec/TopLevelSpec.v Spec/Vst Spec/main.v \
		 Lib/VstLib.v html \
         Spec/Swap_SimpleSpec_Examples.v
OCAMLBUILDFLAGS=-libs unix,str
QC = quickChick -color -top "" -ocamlbuild '$(OCAMLBUILDFLAGS)' \
	 -cmd '$(MAKE) coq-qc' $(QCFLAGS)

coq: Makefile.coq $(EXTR_BIN)
	@$(MAKE) -f $<

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

build-with-vst:
	make -f Makefile.vst build

test:
	$(MAKE) testcoq
	$(MAKE) testexternal

testcoq:
	$(QC) -s CLikeTest -exclude $(EXCLUDE)

testexternal: $(SERVER)
	$(QC) -s ExternalTest -N 100 -exclude $(EXCLUDE)

$(SERVER): DeepWeb/Spec/main.c DeepWeb/Spec/macros.h
	mkdir -p out/
	$(CC) -IDeepWeb/Spec/ $< -o $@

server: $(SERVER) stop
	exec $< &

stop:
	@if [ -n "$$(pgrep $(SERVER))" ]; then pkill $(SERVER); fi

coq-qc: $(SERVER)
	@perl -i -p0e 's/^(Separate Extraction)(\s+\S+)*?((\s+test\S+)*)\s*\.$$/\1\3./m' QuickChickTop.v
	@echo "-Q . ''" > _CoqProject.tmp
	@cat _CoqProject >> _CoqProject.tmp
	@coq_makefile -f _CoqProject.tmp -o Makefile.tmp
	@make -f Makefile.tmp QuickChickTop.vo
	@echo 'let _ = print_endline "done"' >> QuickChickTop.ml

html:
	$(MAKE) -f Makefile.coq -j
	$(MAKE) -f Makefile.coq html

clean:
	-rm -rf ../_qc_dw.tmp/
	$(MAKE) -f Makefile.coq clean

.PHONY: html clean coq-qc test coq

# Just for BCP
bcp:
	$(MAKE) -C $(HOME)/dw/src dsss18
	$(MAKE) -j
	$(MAKE) -j html COQDOCFLAGS="-interpolate -utf8 --parse-comments"
	osascript $(HOME)/s/tools/safari-reload.as
	$(MAKE) -j test

