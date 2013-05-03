# $Id: Makefile,v 1.3 2013-05-03 08:52:51 deraugla Exp $

TARGET=ConvexHull.vo Puiseux.vo InSegment.vo NotInSegment.vo

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
