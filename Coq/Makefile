# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: fiat-crypto saw-script extract CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

saw-script: 
	$(MAKE) -C saw-script/saw-core-coq/coq

fiat-crypto:
	$(MAKE) SKIP_BEDROCK2=1 coq -C fiat-crypto

extract:
	$(MAKE) -C EC

.PHONY: invoke-coqmakefile fiat-crypto saw-script extract $(KNOWNFILES)

####################################################################
##                      Your targets here                         ##
####################################################################


# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
