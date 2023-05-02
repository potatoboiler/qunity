# based on https://coq.inria.fr/refman/practical-tools/utilities.html#building-a-coq-project-with-coq-makefile

KNOWNTARGETS := CoqMakefile

KNOWNFILES := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

clean:
	rm -rf CoqMakefile .CoqMakefile.d CoqMakefile.conf */*.vo* */*/*.vo* */*/*/*.vo* */*.glob */*/*.glob */*/*/*.glob */.*.aux */*/.*.aux */*/*/.*.aux .lia.cache

%: invoke-coqmakefile
	@true

