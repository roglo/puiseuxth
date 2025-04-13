# $Id: Makefile,v 1.1 2013-03-28 13:34:22 deraugla Exp $

all: proof cpoly puiseux
	@echo
	@echo 'available command: puiseux'

clean:
	cd coq; $(MAKE) clean
	cd cpoly; $(MAKE) clean
	cd ocaml; $(MAKE) clean
	rm -f puiseux ugly

cpoly:
	cd cpoly; $(MAKE)

puiseux: cpoly
	cd ocaml; $(MAKE)
	cp ocaml/puiseux .

proof:
	cd coq; $(MAKE)

.PHONY: cpoly puiseux coq
