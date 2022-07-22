COQ_MAKEFILE = "MakefileCoq.mk"

COQ_MAKE = $(MAKE) -f $(COQ_MAKEFILE)

all: $(COQ_MAKEFILE)
	@+$(COQ_MAKE) all

clean: $(COQ_MAKEFILE)
	@+$(COQ_MAKE) cleanall
	@rm -f $(COQ_MAKEFILE) $(COQ_MAKEFILE).conf

$(COQ_MAKEFILE): _CoqProject
	coq_makefile -f _CoqProject -o $(COQ_MAKEFILE)

_CoqProject:
	@echo "-Q src/lf LF" > $@
	@echo "" >> $@
	@find src -iname '*.v' | sort >> $@

%: $(COQ_MAKEFILE)
	@+$(COQ_MAKE) $@

.PHONY: all clean _CoqProject
