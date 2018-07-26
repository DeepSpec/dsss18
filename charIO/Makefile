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

CC_LOC=$(VST_LOC)/compcert

VST_DIRS= msl sepcomp veric floyd progs
VSTFLAGS= -Q $(CC_LOC) compcert $(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d))

vst: Makefile.vst
	$(MAKE) -f Makefile.vst VERBOSE=true

Makefile.vst: _CoqProject.pre
	echo $(VSTFLAGS) > _CoqProject
	cat $^ >> _CoqProject
	coq_makefile -f _CoqProject -o $@ 2>> /tmp/client_error

clean:
	find . -name "*.vo" -print -exec rm -rf {} \;
	find . -name "*.glob" -print -exec rm -rf {} \;
	find . -name ".*.aux" -print -exec rm -rf {} \;
	-$(MAKE) -f Makefile.vst clean;
	rm _CoqProject;
	rm Makefile.vst;
	rm Makefile.vst.conf;
	-rm -rf .coqdeps.d

.PHONY: clean
