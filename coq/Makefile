# $Id: Makefile,v 1.7 2013-07-22 01:10:57 deraugla Exp $

TARGET=PolyConvexHull.vo CharactPolyn.vo Puiseux.vo

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
