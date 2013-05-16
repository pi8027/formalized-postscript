include ./.deps

COQLIBS=-R . FormalPS
VOFILES=$(VFILES:.v=.vo)
GLOBFILES=$(VFILES:.v=.glob)

.DEFAULT_GOAL := all
.PHONY: all clean

all: lib.ps

clean:
	rm -f .deps ${VOFILES} ${GLOBFILES} lib.ps

.deps: ${VFILES}
	coqdep -c -w -slash ${COQLIBS} ${VFILES} > .deps

%.vo %.glob: %.v
	coqc -q ${COQLIBS} $*

lib.ps: embed.m4 lib.ps.m4 ${VFILES} ${VOFILES}
	m4 embed.m4 lib.ps.m4 > lib.ps
