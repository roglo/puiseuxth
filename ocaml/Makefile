# $Id: Makefile,v 1.10 2013-04-06 09:07:58 deraugla Exp $

TARGET=puiseux.out ugly.out
FILES=pnums.cmo poly_lex.cmo poly_parse.cmo poly_print.cmo poly_fun.cmo version.cmo poly_tree.cmo roots.cmo poly.cmo puiseux_series.cmo puiseux.cmo
UFILES=pnums.cmo poly_print.cmo poly_lex.cmo poly_parse.cmo poly_tree.cmo ugly.cmo
FILESFORDEP=`LC_ALL=C ls *.ml *.mli`
TEST_DIR=test `basename "$<"` = "$<" || { echo "File \"$<\" needs to be recompiled."; echo "Please run 'make' in directory '$$(dirname "$<")' first."; exit 1; }
LIB=nums.cma gramlib.cma

MPFR_DIR=
CPOLY_OBJS=../cpoly/ml_mpfr.o ../cpoly/cpoly.cmo
LINKFLAGS= -cclib -L$(MPFR_DIR)/usr/lib -cclib -lmpfr -cclib -lgmp

OCOPT=-I ../cpoly
OCAMLC=ocamlc.opt -g
OCAMLOPT=ocamlopt.opt -w +32
OCAMLOPT=ocamlopt.opt

all: opt

out: q_def_expr.cmo $(TARGET)
	cp puiseux.out puiseux
	cp ugly.out ugly

opt: q_def_expr.cmo $(TARGET:.out=.opt)
	cp puiseux.opt puiseux
	cp ugly.opt ugly

puiseux.cmx: pa_coq.cmo

puiseux.out: $(FILES)
	$(OCAMLC) -custom -I +camlp5 $(CPOLY_OBJS) $(LIB) $(FILES) $(LINKFLAGS) -o $@

puiseux.opt: $(FILES:.cmo=.cmx)
	$(OCAMLOPT) -I +camlp5 $(CPOLY_OBJS:.cmo=.cmx) $(LIB:.cma=.cmxa) $(FILES:.cmo=.cmx) $(LINKFLAGS) -o $@

ugly.out: $(UFILES)
	$(OCAMLC) -custom -I +camlp5 $(CPOLY_OBJS) $(LIB) $(UFILES) $(LINKFLAGS) -o $@

ugly.opt: $(UFILES:.cmo=.cmx)
	$(OCAMLOPT) -I +camlp5 $(CPOLY_OBJS:.cmo=.cmx) $(LIB:.cma=.cmxa) $(UFILES:.cmo=.cmx) $(LINKFLAGS) -o $@

clean:
	rm -f *.cm[iox] *.o *.out *.opt puiseux ugly

depend:
	mv .depend .depend.bak
	@ > .depend
	@for i in $(FILESFORDEP); do \
	  echo "camlp5r pr_depend.cmo -- -I ../cpoly $$i" 1>&2; \
	  camlp5r pr_depend.cmo -- -I ../cpoly $$i; \
	done > .depend

.PHONY: all out opt clean depend
.SUFFIXES: .mli .ml .cmi .cmo .cmx

.mli.cmi:
	@$(TEST_DIR)
	$(OCAMLC) $(OCOPT) -pp camlp5r -I +camlp5 -c $<

.ml.cmo:
	@$(TEST_DIR)
	$(OCAMLC) $(OCOPT) -pp camlp5r -I +camlp5 -c $<

.ml.cmx:
	@$(TEST_DIR)
	$(OCAMLOPT) $(OCOPT) -pp camlp5r -I +camlp5 -c $<

include .depend
