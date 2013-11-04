############################################################################
#
#  Primary targets:
#    all           - the default target; synonym for 'coq'
#    coq           - builds all .vo files
#    clean         - removes generated files
#
############################################################################

## Paths to executables. Do not include options here.
## Modify these to suit your Coq installation, if necessary.

COQC = coqc
COQDEP = coqdep

## List of files to be compiled and documented.

FILES = \
	LibWfenv \
	Core_Definitions \
	Core_Infrastructure \
	Source_Definitions \
	Source_Properties \
	Target_Definitions \
	Target_Properties \
	Cps_Trans

## Lists calculated from the above.

VFILES   = $(foreach i, $(FILES), $(i).v)
VOFILES  = $(foreach i, $(FILES), $(i).vo)

############################################################################

.PHONY: all clean coq
.SUFFIXES: .v .vo

all:
	+make coq

coq: $(VOFILES)

clean:
	rm -f *.vo *.glob

############################################################################

%.vo: %.v
	$(COQC) $<

############################################################################

.depend: $(VFILES)
	$(COQDEP) $(INCFLAGS) $(VFILES) > .depend

include .depend
