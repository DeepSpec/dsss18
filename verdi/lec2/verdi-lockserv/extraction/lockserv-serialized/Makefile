OCAMLBUILD = ocamlbuild -use-ocamlfind -tags 'safe_string thread' -pkgs 'verdi-runtime cheerios-runtime' -I ocaml -cflag -g

MLEXTRACTED = ocaml/LockServSerialized.ml ocaml/LockServSerialized.mli

MLFILES = ocaml/LockServSerializedArrangement.ml ocaml/LockServSerializedMain.ml \
 ocaml/LockServSerializedOpts.ml ocaml/LockServSerializedSerialization.ml

default: LockServSerializedMain.native

$(MLEXTRACTED):
	+$(MAKE) -C ../.. extraction/lockserv-serialized/$@

LockServSerializedMain.native: $(MLEXTRACTED) $(MLFILES) script/remove_module.pl
	perl script/remove_module.pl ocaml/LockServSerialized
	$(OCAMLBUILD) LockServSerializedMain.native

LockServSerializedMain.byte: $(MLEXTRACTED) $(MLFILES) script/remove_module.pl
	perl script/remove_module.pl ocaml/LockServSerialized
	$(OCAMLBUILD) -tag debug LockServSerializedMain.byte

clean:
	ocamlbuild -clean

.PHONY: default clean $(MLEXTRACTED)

.NOTPARALLEL: $(MLEXTRACTED)
