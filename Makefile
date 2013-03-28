# $Id: Makefile,v 1.1 2013-03-28 13:34:22 deraugla Exp $

all: cpoly puiseux
	cp ocaml/puiseux ocaml/ugly .
	@echo
	@echo 'available commands: puiseux, ugly'

clean:
	cd cpoly; $(MAKE) clean
	cd ocaml; $(MAKE) clean
	rm -f puiseux ugly

cpoly:
	cd cpoly; $(MAKE)

puiseux: cpoly
	cd ocaml; $(MAKE)

.PHONY: cpoly puiseux
