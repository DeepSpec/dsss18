OCAMLBUILD = ocamlbuild -use-ocamlfind -tags thread,safe_string -package verdi-runtime -I ocaml -cflag -g
OCAMLBUILD_TEST = $(OCAMLBUILD) -package oUnit -I test

MLEXTRACTED = ocaml/LockServ.ml ocaml/LockServ.mli

MLFILES = ocaml/LockServArrangement.ml ocaml/LockServSerialization.ml \
 ocaml/LockServMain.ml ocaml/LockServOpts.ml

MLFILES_TEST = test/LockServTest.ml test/OptsTest.ml test/SerializationTest.ml

default: LockServMain.native

$(MLEXTRACTED):
	+$(MAKE) -C ../.. extraction/lockserv/$@

LockServMain.native: $(MLEXTRACTED) $(MLFILES)
	$(OCAMLBUILD) LockServMain.native

LockServTest.native: $(MLEXTRACTED) $(MLFILES) $(MLFILES_TEST)
	$(OCAMLBUILD_TEST) LockServTest.native

test: LockServTest.native
	./LockServTest.native

clean:
	ocamlbuild -clean

.PHONY: default clean test $(MLEXTRACTED)

.NOTPARALLEL: LockServMain.native LockServTest.native
.NOTPARALLEL: $(MLEXTRACTED)
