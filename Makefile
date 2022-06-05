COQ_MAKEFILE = "MakefileCoq.mk"

all: $(COQ_MAKEFILE)
	@+$(MAKE) -f $(COQ_MAKEFILE) all

clean: $(COQ_MAKEFILE)
	@+$(MAKE) -f $(COQ_MAKEFILE) cleanall
	@rm -f $(COQ_MAKEFILE) $(COQ_MAKEFILE).conf

$(COQ_MAKEFILE): _CoqProject
	coq_makefile -f _CoqProject -o $(COQ_MAKEFILE)

_CoqProject:
	@echo "-Q src/lf LF" > _CoqProject
	@echo "" >> _CoqProject
	@find src -iname '*.v' | sort >> _CoqProject

%: $(COQ_MAKEFILE)
	@+$(MAKE) -f $(COQ_MAKEFILE) $@

.PHONY: all clean _CoqProject
