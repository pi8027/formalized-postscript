include Makefile_coq

VFILES=Bool.v Core.v Example.v Nat.v Template.v stdlib_ext.v
VOFILES:=$(VFILES:.v=.vo)

.DEFAULT_GOAL := all
.PHONY: all myclean

all: lib.ps

clean: myclean
myclean:
	rm -f lib.ps Makefile_coq

Makefile_coq:
	coq_makefile -R . FormalPS ${VFILES} > Makefile_coq

lib.ps: embed.m4 lib.ps.m4 ${VFILES} ${VOFILES}
	m4 embed.m4 lib.ps.m4 > lib.ps
