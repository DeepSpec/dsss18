-include CONFIGURE
ifeq ($(VST_LOC),)
$(info VST_LOC is not defined!)
$(info Create a CONFIGURE file containing this definition:)
$(info VST_LOC= .../file/path/to/VST)
$(info and optionally (if you have installed CompCert/clightgen) containing this:)
$(info CC_LOC= .../file/path/to/CompCert)
$(info or instead of a CONFIGURE file, you may define these as environment variables.)
$(error "VST_LOC not defined")
endif
ifeq ($(CC_LOC),)
  CC_LOC=$(VST_LOC)/compcert
endif

VST_DIRS= msl sepcomp veric floyd progs
VSTFLAGS= -Q $(CC_LOC) compcert $(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d))

SERVER = out/dw-swap-server
EXCLUDE= Proofs Spec/TopLevelSpec.v Spec/Vst/ Proofs/ Spec/main.v Lib/VstLib.v FreeMonad/
OCAMLBUILDFLAGS=-libs unix,str
MINI_CLIENT = Test/mini_client.native
QC = quickChick -color -top "" -ocamlbuild '$(OCAMLBUILDFLAGS)' \
	 -cmd 'cp ../dw/CONFIGURE .; $(MAKE) coq-qc' $(QCFLAGS) -exclude $(EXCLUDE)

coq: Makefile.coq $(EXTR_BIN)
	@$(MAKE) -f $<

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

_CoqProject: _CoqProject.Minimal _CoqProject.Vst
	echo "$(VSTFLAGS)" > _CoqProject
	cat _CoqProject.Minimal _CoqProject.Vst >> _CoqProject

_CoqProject.Vst:
	touch _CoqProject.Vst

test:
	echo "-Q . ''" > _CoqProject
	cat ../dw/_CoqProject.Minimal >> _CoqProject
	touch _CoqProject.Minimal
	$(QC)
	$(MAKE) stop

$(SERVER): DeepWeb/Spec/main.c DeepWeb/Spec/macros.h
	mkdir -p out/
	$(CC) -IDeepWeb/Spec/ $< -o $@

server: $(SERVER) stop
	exec $< &

stop:
	@if [ -n "$$(pgrep $(SERVER))" ]; then pkill $(SERVER); fi

coq-qc: $(SERVER)
	coq_makefile -f _CoqProject -o Makefile.coq
	$(MAKE) -f Makefile.coq

html:
	$(MAKE) -f Makefile.coq html

clean:
	-rm -rf ../_qc_dw.tmp/
	$(MAKE) -f Makefile.coq clean

.PHONY: html clean coq-qc test coq
