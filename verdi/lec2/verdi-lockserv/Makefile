include Makefile.detect-coq-version

ifeq (,$(filter $(COQVERSION),8.6 8.7 8.8 trunk))
$(error "Verdi Lockserv is only compatible with Coq version 8.6.1 or later")
endif

COQPROJECT_EXISTS := $(wildcard _CoqProject)

ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

CHECKPATH := $(shell ./script/checkpaths.sh)

ifneq ("$(CHECKPATH)","")
$(info $(CHECKPATH))
$(warning checkpath reported an error)
endif

default: Makefile.coq
	$(MAKE) -f Makefile.coq

LOCKSERV_MLFILES = extraction/lockserv/ocaml/LockServ.ml extraction/lockserv/ocaml/LockServ.mli
LOCKSERV_SEQNUM_MLFILES = extraction/lockserv-seqnum/ocaml/LockServSeqNum.ml extraction/lockserv-seqnum/ocaml/LockServSeqNum.mli
LOCKSERV_SER_MLFILES = extraction/lockserv-serialized/ocaml/LockServSerialized.ml extraction/lockserv-serialized/ocaml/LockServSerialized.mli

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq -install none \
          -extra '$(LOCKSERV_MLFILES)' \
	    'extraction/lockserv/coq/ExtractLockServ.v systems/LockServ.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/lockserv/coq/ExtractLockServ.v' \
          -extra '$(LOCKSERV_SEQNUM_MLFILES)' \
	    'extraction/lockserv-seqnum/coq/ExtractLockServSeqNum.v systems/LockServSeqNum.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/lockserv-seqnum/coq/ExtractLockServSeqNum.v' \
          -extra '$(LOCKSERV_SER_MLFILES)' \
	    'extraction/lockserv-serialized/coq/ExtractLockServSerialized.v systems/LockServSerialized.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/lockserv-serialized/coq/ExtractLockServSerialized.v'

$(LOCKSERV_MLFILES) $(LOCKSERV_SEQNUM_MLFILES) $(LOCKSERV_SER_MLFILES): Makefile.coq
	$(MAKE) -f Makefile.coq $@

lockserv:
	+$(MAKE) -C extraction/lockserv

lockserv-test:
	+$(MAKE) -C extraction/lockserv test

lockserv-seqnum:
	+$(MAKE) -C extraction/lockserv-seqnum

lockserv-serialized:
	+$(MAKE) -C extraction/lockserv-serialized

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq
	$(MAKE) -C extraction/lockserv clean
	$(MAKE) -C extraction/lockserv-seqnum clean
	$(MAKE) -C extraction/lockserv-serialized clean

lint:
	@echo "Possible use of hypothesis names:"
	find . -name '*.v' -exec grep -Hn 'H[0-9][0-9]*' {} \;

distclean: clean
	rm -f _CoqProject

.PHONY: default clean lint $(LOCKSERV_MLFILES) $(LOCKSERV_SEQNUM_MLFILES) $(LOCKSERV_SER_MLFILES) lockserv lockserv-test lockserv-seqnum lockserv-serialized
