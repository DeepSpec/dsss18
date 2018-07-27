OCAMLBUILD = ocamlbuild -use-ocamlfind -tags safe_string,thread -package verdi-runtime -I ocaml -cflag -g

MLEXTRACTED = ocaml/LockServSeqNum.ml ocaml/LockServSeqNum.mli

MLFILES = ocaml/LockServSeqNumArrangement.ml ocaml/LockServSeqNumSerialization.ml \
 ocaml/LockServSeqNumMain.ml ocaml/LockServSeqNumOpts.ml

default: LockServSeqNumMain.native

$(MLEXTRACTED):
	+$(MAKE) -C ../.. extraction/lockserv-seqnum/$@

LockServSeqNumMain.native: $(MLEXTRACTED) $(MLFILES)
	$(OCAMLBUILD) LockServSeqNumMain.native

clean:
	ocamlbuild -clean

.PHONY: default clean $(MLEXTRACTED)

.NOTPARALLEL: $(MLEXTRACTED)
