(* $Id: pa_coq.ml,v 1.8 2013-04-19 01:54:40 deraugla Exp $ *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Pcaml;

EXTEND
  GLOBAL: str_item expr patt;
  str_item:
    [ [ "Fixpoint"; l = V (LIST1 coq_binding SEP "and") →
          <:str_item< value rec $_list:l$ >>
      | "Definition"; l = V (LIST1 coq_binding SEP "and") →
          <:str_item< value $_list:l$ >> ] ]
  ;
  coq_binding:
    [ [ p = ipatt; e = coq_fun_binding → (p, e) ] ]
  ;
  coq_fun_binding:
    [ RIGHTA
      [ p = ipatt; e = SELF → <:expr< fun $p$ → $e$ >>
      | ":="; e = coq_expr → <:expr< $e$ >>
      | ":"; t = ctyp; ":="; e = coq_expr → <:expr< ($e$ : $t$) >> ] ]
  ;
  coq_expr:
    [ [ "match"; e = SELF; "with"; l = V (LIST0 coq_match_case); "end" →
          <:expr< match $e$ with [ $_list:l$ ] >>
      | "let"; r = V (FLAG "fix"); l = V (LIST1 coq_binding SEP "and"); "in";
        x = SELF →
          <:expr< let $_flag:r$ $_list:l$ in $x$ >>
      | "if"; e1 = SELF; "then"; e2 = SELF; "else"; e3 = SELF →
          <:expr< if $e1$ then $e2$ else $e3$ >>
      | "{|"; lel = V (LIST1 coq_label_expr SEP ";"); "|}" →
          <:expr< { $_list:lel$ } >>
      | e = expr →
          e ] ]
  ;
  expr: BEFORE "simple"
    [ [ e = expr; "%"; LIDENT "nat" → e ] ]
  ;
  expr: LEVEL "simple"
    [ [ "("; GIDENT "λ"; p = ipatt; ","; e = coq_expr; ")" →
          <:expr< fun $p$ → $e$ >>
      | UIDENT "Qle_bool" →
          <:expr< Q.le >>
      | UIDENT "Qeq_bool" →
          <:expr< Q.eq >>
      | UIDENT "S" →
          <:expr< succ >> ] ]
  ;
  patt: LEVEL "simple"
    [ [ UIDENT "O" → <:patt< 0 >> ] ]
  ;
  coq_match_case:
    [ [ "|"; p = patt; "=>"; e = coq_expr →
        let (p, e) =
          match p with
          [ <:patt< S $lid:n$ >> →
              (<:patt< $lid:n$ >>,
               <:expr< let $lid:n$ = pred $lid:n$ in $e$ >>)
          | _ →
              (p, e) ]
        in
        (p, <:vala< None >>, e) ] ]
  ;
  coq_label_expr:
    [ [ i = patt_label_ident; e = coq_fun_binding → (i, e) ] ]
  ;
  patt_label_ident:
    [ LEFTA
      [ p1 = SELF; "."; p2 = SELF → <:patt< $p1$ . $p2$ >> ]
    | "simple" RIGHTA
      [ i = V UIDENT → <:patt< $_uid:i$ >>
      | i = V LIDENT → <:patt< $_lid:i$ >>
      | "_" → <:patt< _ >> ] ]
  ;
END;
