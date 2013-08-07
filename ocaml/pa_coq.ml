(* $Id: pa_coq.ml,v 1.58 2013-08-07 01:02:16 deraugla Exp $ *)

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

value mklistexp loc last =
  loop True where rec loop top =
    fun
    [ [] ->
        match last with
        [ Some e -> e
        | None -> <:expr< [] >> ]
    | [e1 :: el] ->
        let loc =
          if top then loc else Ploc.encl (MLast.loc_of_expr e1) loc
        in
        <:expr< [$e1$ :: $loop False el$] >> ]
;

value mklistpat loc last =
  loop True where rec loop top =
    fun
    [ [] ->
        match last with
        [ Some p -> p
        | None -> <:patt< [] >> ]
    | [p1 :: pl] ->
        let loc =
          if top then loc else Ploc.encl (MLast.loc_of_patt p1) loc
        in
        <:patt< [$p1$ :: $loop False pl$] >> ]
;

value lazy_if_type n t =
  match t with
  [ <:ctyp:< $lid:m$ $p$ >> → if m = n then <:ctyp< Lazy.t $t$ >> else t
  | _ → t ]
;

value add_lazy_t (_, n) (loc, ci, tl, b) =
  let tl = List.map (lazy_if_type (unvala n)) (unvala tl) in
  (loc, ci, <:vala< tl >>, b)
;

EXTEND
  GLOBAL: str_item expr patt ctyp;
  str_item:
    [ [ "Fixpoint"; l = V (LIST1 coq_binding SEP "and") →
          <:str_item< value rec $_list:l$ >>
      | "CoFixpoint"; l = V (LIST1 coq_binding SEP "and") →
          <:str_item< value rec $_list:l$ >>
      | "Definition"; l = V (LIST1 coq_binding SEP "and") →
          <:str_item< value $_list:l$ >>
      | "Inductive"; n = V type_patt "tp"; tpl = V (LIST0 type_parameter);
        ":="; cdl = V (LIST0 coq_constr_decl) →
          <:str_item< type $_tp:n$ $_list:tpl$ = [ $_list:cdl$ ] >>
      | "CoInductive"; n = V type_patt "tp"; tpl = V (LIST0 type_parameter);
        ":="; cdl = V (LIST0 coq_constr_decl) →
          let cdl = List.map (add_lazy_t (unvala n)) (unvala cdl) in
          <:str_item< type $_tp:n$ $_list:tpl$ = [ $list:cdl$ ] >>
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
(*
                let e =
                  List.fold_right (fun _ e → <:expr< fun () → $e$ >>)
                    (unvala tpl) e
                in
*)
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
  ctyp: LEVEL "apply"
    [ [ LIDENT "field"; v = NEXT → <:ctyp< field $v$ β >> ] ]
  ;
  ctyp: LEVEL "simple"
    [ [ UIDENT "Q" → <:ctyp< Q.t >>
      | UIDENT "Z" → <:ctyp< I.t >>
      | LIDENT "positive" → <:ctyp< I.t >>
      | LIDENT "nat" → <:ctyp< int >> ] ]
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
    [ [ p = ipatt; LIST0 GIDENT; e = coq_fun_binding → (p, e) ] ]
  ;
  coq_fun_binding:
    [ RIGHTA
      [ "("; pl = LIST1 LIDENT; ":"; t = ctyp; ")"; e = SELF →
          List.fold_right (fun p e → <:expr< fun ($lid:p$ : $t$) → $e$ >>)
            pl e
      | p = ipatt; e = SELF → <:expr< fun $p$ → $e$ >>
      | ":="; e = coq_expr → <:expr< $e$ >>
      | ":"; t = ctyp; ":="; e = coq_expr → <:expr< ($e$ : $t$) >> ] ]
  ;
  coq_expr:
    [ [ "match"; e = SELF; "with"; l = V (LIST0 coq_match_case); "end" →
          match unvala l with
          | [(<:patt< Z0 >>, _, _) :: _] →
              <:expr< match zcoq $e$ with [ $_list:l$ ] >>
          | _ →
              <:expr< match $e$ with [ $_list:l$ ] >>
          end
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
  expr: LEVEL "."
    [ [ UIDENT "Decidable"; "."; LIDENT "dec_and" →
          <:expr< $lid:"&&"$ >>
      | UIDENT "Z"; "."; LIDENT "add" →
          <:expr< I.add >>
      | UIDENT "Z"; "."; LIDENT "sub" →
          <:expr< I.sub >>
      | UIDENT "Z"; "."; LIDENT "mul" →
          <:expr< I.mul >>
      | UIDENT "Z"; "."; LIDENT "succ" →
          <:expr< I.succ >>
      | UIDENT "Z"; "."; LIDENT "min" →
          <:expr< I.min >>
      | UIDENT "Z"; "."; LIDENT "of_nat" →
          <:expr< I.of_int >>
      | UIDENT "Z"; "."; LIDENT "to_nat" →
          <:expr< I.to_int >>
      | UIDENT "Pos"; "."; LIDENT "to_nat" →
          <:expr< I.to_int >>
      | UIDENT "Pos"; "."; LIDENT "mul" →
          <:expr< I.mul >> ] ]
  ;
  expr: LEVEL "apply"
    [ [ UIDENT "Term"; e₁ = NEXT; e₂ = NEXT →
          <:expr< Term $e₁$ (lazy $e₂$) >>
      | UIDENT "Zpos"; e = NEXT →
          e
      | LIDENT "zerop"; e = NEXT →
         <:expr< $e$ = 0 >>
      | e = SELF; "_" →
          e ] ]
  ;
  expr: BEFORE "simple"
    [ [ e = expr; "%"; LIDENT "nat" → e
      | e = expr; "%"; LIDENT "positive" → e ] ]
  ;
  expr: LEVEL "simple"
    [ [ GIDENT "λ"; p = ipatt; e = coq_fun_def →
          <:expr< fun $p$ → $e$ >>
      | "{|"; lel = V (LIST1 coq_label_expr SEP ";"); "|}" →
          <:expr< { $_list:lel$ } >>
      | "["; el = LIST1 expr SEP ";"; last = cons_expr_opt; "]" ->
          mklistexp loc last el
      | UIDENT "Qlt_le_dec" →
         <:expr< Q.lt >>
      | LIDENT "eq_nat_dec" →
         <:expr< $lid:"="$ >>
      | LIDENT "lt_dec" →
         <:expr< $lid:"<"$ >>
      | LIDENT "gt_dec" →
         <:expr< $lid:">"$ >>
      | UIDENT "Plcm" →
          <:expr< I.lcm >>
      | UIDENT "Qeq_bool" →
         <:expr< Q.eq >>
      | UIDENT "Qle_bool" →
         <:expr< Q.le >>
      | UIDENT "Qmake" →
          <:expr< Q.make >>
      | UIDENT "Qcompare" →
          <:expr< qcompare >>
      | UIDENT "Qmult" →
          <:expr< Q.mul >>
      | UIDENT "Qdiv" →
          <:expr< Q.div >>
      | UIDENT "Qplus" →
          <:expr< Q.add >>
      | UIDENT "Qminus" →
          <:expr< Q.sub >>
      | UIDENT "Qopp" →
          <:expr< Q.neg >>
      | UIDENT "Qnum" →
          <:expr< Q.rnum >>
      | UIDENT "Qden" →
          <:expr< Q.rden >>
      | UIDENT "Qred" →
          <:expr< Q.norm >>
      | UIDENT "Qnat" →
          <:expr< qnat >>
      | LIDENT "inject_Z" →
          <:expr< Q.of_i >>
      | UIDENT "Z_lt_le_dec" →
         <:expr< I.lt >>
      | UIDENT "Zcompare" →
          <:expr< zcompare >>
      | UIDENT "O" →
          <:expr< 0 >>
      | UIDENT "S" →
          <:expr< succ >>
      | LIDENT "negb" →
          <:expr< not >>
      | LIDENT "false" →
          <:expr< False >>
      | LIDENT "true" →
          <:expr< True >> ] ]
  ;
  patt: LEVEL "simple"
    [ [ "["; pl = LIST1 patt SEP ";"; last = cons_patt_opt; "]" ->
          mklistpat loc last pl ] ]
  ;
  cons_patt_opt:
    [ [ "…"; p = patt -> Some p
      | -> None ] ]
  ;
  cons_expr_opt:
    [ [ "…"; e = expr -> Some e
      | -> None ] ]
  ;
  coq_fun_def:
    [ RIGHTA
      [ p = ipatt; e = SELF -> <:expr< fun $p$ -> $e$ >>
      | ","; e = coq_expr -> e ] ]
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
          | <:patt< Term $p₁$ $lid:n$ >> →
              (<:patt< Term $p₁$ $lid:n$ >>,
               <:expr< let $lid:n$ = Lazy.force $lid:n$ in $e$ >>)
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
