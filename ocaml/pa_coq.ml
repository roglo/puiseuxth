(* $Id: pa_coq.ml,v 1.11 2013-04-21 01:01:51 deraugla Exp $ *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Pcaml;

value fun_decl_of_label (loc, i, _, _) =
  <:str_item< value $lid:i$ x = x.$lid:i$ >>
;

EXTEND
  GLOBAL: str_item expr patt ctyp;
  str_item:
    [ [ "Fixpoint"; l = V (LIST1 coq_binding SEP "and") →
          <:str_item< value rec $_list:l$ >>
      | "Definition"; l = V (LIST1 coq_binding SEP "and") →
          <:str_item< value $_list:l$ >>
      | "Record"; n = V type_patt "tp"; tpl = V (LIST0 type_parameter); ":=";
        "{"; ldl = V (LIST1 label_declaration SEP ";"); "}" ->
          let tk = <:ctyp< { $_list:ldl$ } >> in
          let d = <:str_item< type $_tp:n$ $_list:tpl$ = $tk$ >> in
          let dl = List.map fun_decl_of_label (unvala ldl) in
          <:str_item< declare $list:[d :: dl]$ end >> ] ]
  ;
  label_declaration:
    [ [ i = LIDENT; ":"; t = ctyp -> (loc, i, False, t) ] ]
  ;
  type_patt:
    [ [ n = V LIDENT -> (loc, n) ] ]
  ;
  type_parameter:
    [ [ i = GIDENT -> (<:vala< Some (greek_ascii_equiv i) >>, None) ] ]
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
      | e = expr →
          e ] ]
  ;
  expr: BEFORE "simple"
    [ [ e = expr; "%"; LIDENT "nat" → e ] ]
  ;
  expr: LEVEL "simple"
    [ [ "("; GIDENT "λ"; p = ipatt; ","; e = coq_expr; ")" →
          <:expr< fun $p$ → $e$ >>
      | "{|"; lel = V (LIST1 coq_label_expr SEP ";"); "|}" →
          <:expr< { $_list:lel$ } >>
      | UIDENT "Qcompare" →
          <:expr< qcompare >>
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
  ctyp: LEVEL "simple"
    [ [ LIDENT "nat" → <:ctyp< int >> ] ]
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
