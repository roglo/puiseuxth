# $Id: Makefile,v 1.6 2013-06-20 02:30:32 deraugla Exp $

TARGET=PolyConvexHull.vo Puiseux.vo

FILESFORDEP=`LC_ALL=C ls *.v`

all: $(TARGET)

clean:
	rm -f *.glob *.vo
	rm -f *.cm[iox] *.o *.cmxs *.native

depend:
	mv .depend .depend.bak
	coqdep -I . $(FILESFORDEP) | LC_ALL=C sort > .depend

.SUFFIXES: .v .vo

.v.vo:
	coqc $<

include .depend
