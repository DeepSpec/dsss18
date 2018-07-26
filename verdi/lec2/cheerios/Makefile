include Makefile.detect-coq-version

ifeq (,$(filter $(COQVERSION),8.6 8.7 8.8 trunk))
$(error "Cheerios is only compatible with Coq version 8.6.1 or later")
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

MLPOSITIVE = runtime/test/positive_serializer.ml runtime/test/positive_serializer.mli
MLTREE = runtime/test/tree_serializer.ml runtime/test/tree_serializer.mli

default: Makefile.coq
	$(MAKE) -f Makefile.coq

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq \
	  -extra '$(MLPOSITIVE)' \
	    'runtime/coq/ExtractPositiveSerializer.v runtime/coq/ExtractPositiveSerializerDeps.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) runtime/coq/ExtractPositiveSerializer.v' \
	  -extra '$(MLTREE)' \
	    'runtime/coq/ExtractTreeSerializer.v runtime/coq/ExtractTreeSerializerDeps.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) runtime/coq/ExtractTreeSerializer.v'	

$(MLPOSITIVE) $(MLTREE): Makefile.coq
	$(MAKE) -f Makefile.coq $@

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq
	$(MAKE) -C runtime clean

distclean: clean
	rm -f _CoqProject

.PHONY: default clean install distclean quick

.NOTPARALLEL: $(MLPOSITIVE)
.NOTPARALLEL: $(MLTREE)
