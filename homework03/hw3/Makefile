.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile:  CoqMakefile
	$(MAKE) -f CoqMakefile

clean: CoqMakefile
	$(MAKE) -f CoqMakefile clean

.PHONY: invoke-coqmakefile
