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

invoke-coqmakefile: CoqMakefile
		$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES) docs

####################################################################
##                      Your targets here                         ##
####################################################################

	# this redirects to the current version of mathcomp 
	# --external 'http://math-comp.github.io/htmldoc/' mathcomp  \

docs:
	rm -rf docs && mkdir docs 
	rocq doc --html \
	--coqlib_url https://rocq-prover.org/doc/V9.0.0/corelib \
	--external 'http://math-comp.github.io/htmldoc/' mathcomp  \
	-d ./docs \
	-R src/ RDF \
	$$(cat _CoqProject | grep -v "^#" | grep "\.v$$")
	

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
		@true
