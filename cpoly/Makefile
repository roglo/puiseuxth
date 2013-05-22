# $Id: Makefile,v 1.2 2013-05-22 03:45:46 deraugla Exp $

OBJS=cpoly.cmo main.cmo

MPFR_OBJS=ml_mpfr.o
FILESFORDEP=`LC_ALL=C ls *.ml *.mli`
OCAMLLIB=`ocamlc -where`
MPFR_DIR=
MPFR_INCLUDE=-I$(MPFR_DIR)/usr/include
LINKFLAGS= -cclib -L$(MPFR_DIR)/usr/lib -cclib -lmpfr -cclib -lgmp
TOPNAME=ocaml_mpfr
OTHER_OBJS=

all: opt top

clean:
	rm -f *.out *.opt *.cm[iox] *.o ocaml_mpfr cpolyc

depend:
	mv .depend .depend.bak
	@ > .depend
	@for i in $(FILESFORDEP); do \
	  echo "camlp5r pr_depend.cmo -I . $$i" 1>&2; \
	  camlp5r pr_depend.cmo -I . $$i; \
	done > .depend

opt: cpolyc.opt
	cp $< cpolyc

out: cpolyc.out
	cp $< cpolyc

cpolyf.out: cpoly.f
	f77 cpoly.f -o $@

cpolyc.out: $(OBJS) ml_mpfr.o
	ocamlc -custom $(MPFR_OBJS) $(OBJS) $(LINKFLAGS) -o $@

cpolyc.opt: $(OBJS:.cmo=.cmx) ml_mpfr.o
	ocamlopt $(MPFR_OBJS) $(OBJS:.cmo=.cmx) $(LINKFLAGS) -o $@

top: $(TOPNAME)

$(TOPNAME): cpoly.cmo ml_mpfr.o
	ocamlmktop -custom $(MPFR_OBJS) $(OTH_OBJS) cpoly.cmo $(LINKFLAGS) -o $(TOPNAME)

ml_mpfr.o: ml_mpfr.c
	$(CC) -c -I$(OCAMLLIB) $(MPFR_INCLUDE) $<

.PHONY: all clean depend out opt top

.SUFFIXES: .ml .mli .cmo .cmx .cmi

.mli.cmi:
	ocamlc -pp camlp5r -c $<

.ml.cmo:
	ocamlc -pp camlp5r -c $<

.ml.cmx:
	ocamlopt -pp camlp5r -c $<

include .depend
