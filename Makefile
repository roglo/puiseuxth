# $Id: Makefile,v 1.1 2013-03-28 13:34:22 deraugla Exp $

all: cpoly puiseux proof

clean:
	cd cpoly; $(MAKE) clean
	cd ocaml; $(MAKE) clean
	cd coq; $(MAKE) clean
	rm -f puiseux ugly

cpoly:
	cd cpoly; $(MAKE)

puiseux: cpoly
	cp ocaml/puiseux .
	@echo
	@echo 'available command: puiseux'

proof:
	cd coq; $(MAKE)

.PHONY: cpoly puiseux coq
