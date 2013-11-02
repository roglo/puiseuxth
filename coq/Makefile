# $Id: Makefile,v 2.0 2013-11-02 01:12:58 deraugla Exp $

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
