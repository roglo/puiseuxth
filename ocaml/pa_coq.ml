(* $Id: pa_coq.ml,v 1.26 2013-05-30 08:13:59 deraugla Exp $ *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Pcaml;

value fun_decl_of_label (loc, i, _, _) =
  <:str_item< value $lid:i$ x = x.$lid:i$ >>
;

value rec generalized_type_of_type =
  fun
  [ <:ctyp< $t1$ -> $t2$ >> ->
      let (tl, rt) = generalized_type_of_type t2 in
      ([t1 :: tl], rt)
  | t ->
      ([], t) ]
;

EXTEND
  GLOBAL: str_item expr patt ctyp;
  str_item:
    [ [ "Fixpoint"; l = V (LIST1 coq_binding SEP "and") →
          <:str_item< value rec $_list:l$ >>
      | "Definition"; l = V (LIST1 coq_binding SEP "and") →
          <:str_item< value $_list:l$ >>
      | "Inductive"; n = V type_patt "tp"; tpl = V (LIST0 type_parameter);
        ":="; cdl = V (LIST0 coq_constr_decl) →
          <:str_item< type $_tp:n$ $_list:tpl$ = [ $_list:cdl$ ] >>
      | "Record"; n = V type_patt "tp"; tpl = V (LIST0 type_parameter); ":=";
        c = OPT LIDENT; "{"; ldl = V (LIST1 label_declaration SEP ";"); "}" →
          let tk = <:ctyp< { $_list:ldl$ } >> in
          let d = <:str_item< type $_tp:n$ $_list:tpl$ = $tk$ >> in
          let dl = List.map fun_decl_of_label (unvala ldl) in
          let dl =
            match c with
            | Some c →
                let ll =
                  List.map
                    (fun (loc, i, _, _) →
                       (<:patt< $lid:i$ >>, <:expr< $lid:i$ >>))
                    (unvala ldl)
                in
                let e =
                  List.fold_right
                    (fun (loc, i, _, _) e → <:expr< fun $lid:i$ → $e$ >>)
                    (unvala ldl) <:expr< {$list:ll$} >>
                in
                let e =
                  List.fold_right (fun _ e → <:expr< fun () → $e$ >>)
                    (unvala tpl) e
                in
                let d = <:str_item< value $lid:c$ = $e$ >> in
                [d :: dl]
            | None → dl
            end
          in
          <:str_item< declare $list:[d :: dl]$ end >> ] ]
  ;
  coq_constr_decl:
    [ [ "|"; ci = V UIDENT "uid"; ":"; t = ctyp →
        let (tl, rt) = generalized_type_of_type t in
        (loc, ci, <:vala< tl >>, None) ] ]
  ;
  label_declaration:
    [ [ i = label_ident; ":"; t = ctyp -> (loc, i, False, t) ] ]
  ;
  ctyp: LEVEL "simple"
    [ [ UIDENT "Q" → <:ctyp< Q.t >> ] ]
  ;
  label_ident:
    [ [ i = LIDENT → i
      | i = GIDENT → i ] ]
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
      | "let"; r = fix_or_cofix; l = V (LIST1 coq_binding SEP "and"); "in";
        x = SELF →
          <:expr< let $flag:r$ $_list:l$ in $x$ >>
      | "if"; e1 = SELF; "then"; e2 = SELF; "else"; e3 = SELF →
          <:expr< if $e1$ then $e2$ else $e3$ >>
      | e = expr →
          e ] ]
  ;
  fix_or_cofix:
    [ [ "fix" → True
      | "cofix" → True
      | → False ] ]
  ;
  expr: LEVEL "apply"
    [ [ UIDENT "Term"; e₁ = NEXT; e₂ = NEXT →
          <:expr< Term $e₁$ (lazy $e₂$) >> ] ]
  ;
  expr: BEFORE "simple"
    [ [ e = expr; "%"; LIDENT "nat" → e ] ]
  ;
  expr: LEVEL "simple"
    [ [ "("; GIDENT "λ"; p = ipatt; e = coq_fun_def; ")" →
          <:expr< fun $p$ → $e$ >>
      | "{|"; lel = V (LIST1 coq_label_expr SEP ";"); "|}" →
          <:expr< { $_list:lel$ } >>
      | LIDENT "eq_nat_dec" →
         <:expr< $lid:"="$ >>
      | UIDENT "Qeq_bool" →
         <:expr< $lid:"="$ >>
      | UIDENT "Qcompare" →
          <:expr< qcompare >>
      | UIDENT "Qdiv" →
          <:expr< Q.div >>
      | UIDENT "Qplus" →
          <:expr< Q.add >>
      | UIDENT "Qminus" →
          <:expr< Q.sub >>
      | UIDENT "Qnum" →
          <:expr< Q.rnum >>
      | UIDENT "Qnat" →
          <:expr< qnat >>
      | UIDENT "O" →
          <:expr< 0 >>
      | UIDENT "S" →
          <:expr< succ >> ] ]
  ;
  coq_fun_def:
    [ RIGHTA
      [ p = ipatt; e = SELF -> <:expr< fun $p$ -> $e$ >>
      | ","; e = coq_expr -> e ] ]
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
