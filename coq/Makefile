# $Id: Makefile,v 2.1 2013-12-19 19:25:10 deraugla Exp $

TARGET=Puiseux.vo

FILESFORDEP=`LC_ALL=C ls *.v`

all: $(TARGET)

clean:
	rm -f *.glob *.vo .*.aux *.vok *.vos .lia.cache
	rm -f *.cm[iox] *.o *.cmxs *.native

depend:
	mv .depend .depend.bak
	coqdep -Q . . $(FILESFORDEP) | LC_ALL=C sort > .depend

.SUFFIXES: .v .vo

.v.vo:
	coqc $<

include .depend
