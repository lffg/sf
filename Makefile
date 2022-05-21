COQ_MAKEFILE = "MakefileCoq.mk"

all: $(COQ_MAKEFILE)
	@+$(MAKE) -f $(COQ_MAKEFILE) all

clean: $(COQ_MAKEFILE)
	@+$(MAKE) -f $(COQ_MAKEFILE) cleanall
	@rm -f $(COQ_MAKEFILE) $(COQ_MAKEFILE).conf

$(COQ_MAKEFILE): _CoqProject
	coq_makefile -f _CoqProject -o $(COQ_MAKEFILE)

force _CoqProject Makefile: ;

%: $(COQ_MAKEFILE) force
	@+$(MAKE) -f $(COQ_MAKEFILE) $@

.PHONY: all clean force
