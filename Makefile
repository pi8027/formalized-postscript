.DEFAULT_GOAL := all
.PHONY: all

all: lib.ps

lib.ps: embed.m4 lib.ps.m4
	cat embed.m4 lib.ps.m4 | m4 > lib.ps
