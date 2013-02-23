include ./.deps

COQLIBS=-R . FormalPS
VFILES=Bool.v Core.v Example.v Nat.v Template.v stdlib_ext.v
VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)

.DEFAULT_GOAL := all
.PHONY: all clean

clean:
	rm -f .deps ${VOFILES} ${GLOBFILES} lib.ps

all: lib.ps

.deps: ${VFILES}
	coqdep -c -w -slash ${COQLIBS} ${VFILES} > .deps

%.vo %.glob: %.v
	coqc -q ${COQLIBS} $*

lib.ps: embed.m4 lib.ps.m4 ${VFILES} ${VOFILES}
	m4 embed.m4 lib.ps.m4 > lib.ps
