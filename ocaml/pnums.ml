(* $Id: pnums.ml,v 1.37 2013-04-01 17:37:05 deraugla Exp $ *)

#load "q_MLast.cmo";
#load "./q_def_expr.cmo";

open Printf;

value not_impl name x = do {
  let desc =
    if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  print_newline ();
  failwith ("puiseux: not impl " ^ name ^ " " ^ desc)
};

value sup_txt = [| "⁰"; "¹"; "²"; "³"; "⁴"; "⁵"; "⁶"; "⁷"; "⁸"; "⁹" |];
value inf_txt = [| "₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉" |];

value sup_string_of_string n =
  loop "" 0 where rec loop s i =
    if i = String.length n then s
    else
      match n.[i] with
      [ '0'..'9' as c →
          loop (s ^ sup_txt.(Char.code c - Char.code '0')) (i + 1)
      | '/' → loop (s ^ "ᐟ") (i + 1)
      | '-' → loop (s ^ "⁻") (i + 1)
      | _ → n ]
;
value inf_string_of_string n =
  loop "" 0 where rec loop s i =
    if i = String.length n then s
    else
      match n.[i] with
      [ '0'..'9' as c →
          loop (s ^ inf_txt.(Char.code c - Char.code '0')) (i + 1)
      | _ → n ]
;

value loc = Ploc.dummy;

value rec gcd p q = if q = 0 then p else gcd q (p mod q);
value lcm p q = p / gcd p q * q;
value ios s = try int_of_string s with [ Failure _ → failwith ("ios " ^ s) ];
value soi = string_of_int;
value sof = string_of_float;

exception Overflow;

module I_min =
  struct
    type t = int;
    value make i = i;
    value zero = 0;
    value one = 0;
    value two = 2;
    value minus_one = -1;
    value succ = succ;
    value pred = pred;
    value neg i = -i;
    value abs = abs;
    value add i j =
      let r = i + j in
      if i > 0 && j > 0 && r ≤ 0 || i < 0 && j < 0 && r ≥ 0 then do {
(*
        eprintf "*** plus overflow:\n%!";
        eprintf "(%d) + (%d) = %d\n%!" i j r;
*)
        raise Overflow;
      }
      else r
    ;
    value sub i j =
      let r = i - j in
      if i > 0 && j < 0 && r < 0 || i < 0 && j > 0 && r > 0 then do {
(*
        eprintf "*** minus overflow:\n%!";
        eprintf "(%d) - (%d) = %d\n%!" i j r;
*)
        raise Overflow;
      }
      else r
    ;
    value mul i j =
      let r = i * j in
      if i > 0 && j > 0 && r ≤ 0 || i < 0 && j < 0 && r ≤ 0 then do {
(*
        eprintf "*** mult overflow:\n%!";
        eprintf "(%d) * (%d) = %d\n%!" i j r;
*)
        raise Overflow;
      }
      else r
    ;
    value muli = mul;
    value div i j = i / j;
    value modi i j = i mod j;
    value modn i j = i mod j;
    value incr = incr;
    value eq i j = i = j;
    value lt i j = i < j;
    value gt i j = i > j;
    value ge i j = i ≥ j;
    value gcd = gcd;
    value lcm = lcm;
    value os = int_of_string;
    value ts = string_of_int;
  end;

module I_bignum =
  struct
    open Big_int;
    type t = big_int;
    value of_int = big_int_of_int;
    value to_int = int_of_big_int;
    value zero = zero_big_int;
    value one = unit_big_int;
    value two = of_int 2;
    value minus_one = of_int (-1);
    value neg = minus_big_int;
    value abs = abs_big_int;
    value succ = succ_big_int;
    value pred = pred_big_int;
    value add = add_big_int;
    value sub = sub_big_int;
    value mul = mult_big_int;
    value muli i j = mult_int_big_int j i;
    value div = div_big_int;
    value modi i j = int_of_big_int (mod_big_int i (of_int j));
    value modn = mod_big_int;
    value incr r = r.val := succ r.val;
    value compare = compare_big_int;
    value is_neg x = compare_big_int x zero < 0;
    value eq = eq_big_int;
    value lt = lt_big_int;
    value gt = gt_big_int;
    value ge = ge_big_int;
    value gcd = gcd_big_int;
    value lcm i j = mult_big_int i (div_big_int j (gcd i j));
    value to_float = float_of_big_int;
    value os = big_int_of_string;
    value ts = string_of_big_int;
  end;

(*
module I = I_min;
*)
module I = I_bignum;
(**)

module Q =
  struct
    type t = { rnum : I.t; rden : I.t };
    value rnum r = r.rnum;
    value rden r = r.rden;
    value make n d =
      if I.lt d I.zero then {rnum = I.neg n; rden = I.neg d}
      else {rnum = n; rden = d}
    ;
    value to_string r =
      if I.eq r.rden I.one then I.ts r.rnum
      else sprintf "%s/%s" (I.ts r.rnum) (I.ts r.rden)
    ; 
    value of_i n = {rnum = n; rden = I.one};
    value zero = of_i I.zero;
    value one = of_i I.one;
    value minus_one = of_i I.minus_one;
    value norm r =
      let g = I.gcd (I.abs r.rnum) (I.abs r.rden) in
      let _ = assert (not (I.eq g I.zero)) in
      make (I.div r.rnum g) (I.div r.rden g)
    ;
    value neg r = make (I.neg r.rnum) r.rden;
    value is_neg r = I.is_neg r.rnum <> I.is_neg r.rden;
    value add r₁ r₂ =
      make (I.add (I.mul r₁.rnum r₂.rden) (I.mul r₂.rnum r₁.rden))
        (I.mul r₁.rden r₂.rden)
    ;
    value addi r i =
      make (I.add r.rnum (I.mul i r.rden)) r.rden
    ;
    value sub r₁ r₂ =
      make (I.sub (I.mul r₁.rnum r₂.rden) (I.mul r₂.rnum r₁.rden))
        (I.mul r₁.rden r₂.rden)
    ;
    value mul r₁ r₂ =
      norm (make (I.mul r₁.rnum r₂.rnum) (I.mul r₁.rden r₂.rden))
    ;
    value muli r i =
      make (I.mul r.rnum i) r.rden
    ;
    value div r₁ r₂ =
      make (I.mul r₁.rnum r₂.rden) (I.mul r₁.rden r₂.rnum)
    ;
    value divi r i =
      make r.rnum (I.mul r.rden i)
    ;
    value compare r₁ r₂ =
      let d = I.sub (I.mul r₁.rnum r₂.rden) (I.mul r₁.rden r₂.rnum) in
      if I.lt d I.zero then -1
      else if I.gt d I.zero then 1
      else 0
    ;
    value eq r₁ r₂ = compare r₁ r₂ = 0;
    value le r₁ r₂ = compare r₁ r₂ ≤ 0;
    value lt r₁ r₂ = compare r₁ r₂ < 0;
    value min r₁ r₂ = if le r₁ r₂ then r₁ else r₂;
    value max r₁ r₂ = if le r₁ r₂ then r₂ else r₁;
    value of_expr_if_any =
      fun
      [ << $int:n$ >> → Some (of_i (I.os n))
      | << - $int:n$ >> → Some (of_i (I.neg (I.os n)))
      | << $int:n$ / $int:d$  >> → Some (make (I.os n) (I.os d))
      | << - ($int:n$ / $int:d$)  >> → Some (make (I.neg (I.os n)) (I.os d))
      | _ → None ]
    ;
    value to_float r = I.to_float r.rnum /. I.to_float r.rden;
    value of_expr e =
      match of_expr_if_any e with
      [ Some q → q
      | None →
          match e with
          [ << $lid:s$ $_$ $_$ >> →
              failwith (sprintf "Q.of_expr app(%s,_,_)" s)
          | x → not_impl "Q.of_expr" x ] ]
    ;
    value to_expr q =
      if I.eq q.rden I.one then << $int:I.ts q.rnum$ >>
      else << $int:I.ts q.rnum$ / $int:I.ts q.rden$ >>
    ;
  end;

value find_sqrt a =
  let lim = I.of_int 200000 in
  loop I.two a where rec loop d a =
    if I.gt d lim then (a, I.one)
    else
      let q = I.div a d in
      if I.lt q d then (a, I.one)
      else if I.eq (I.modn a d) I.zero then
        let (b, s) = loop d q in
        if I.eq (I.modn b d) I.zero then (I.div b d, I.mul s d)
        else (I.mul b d, s)
      else loop (I.succ d) a
;

type complex α = Cpoly.complex α == { re : α; im : α };

module A₂ =
  struct
    (* a + b √d *)
    type t = { a : Q.t; b : Q.t; d : I.t };
    value check x =
      if I.eq x.d I.zero then assert (Q.eq x.b Q.zero)
      else if Q.eq x.b Q.zero then assert (I.eq x.d I.zero)
      else ()
    ;
    value make a b d = {a = a; b = b; d = d};
    value zero = make Q.zero Q.zero I.zero;
    value one = make Q.one Q.zero I.zero;
    value minus_one = make Q.minus_one Q.zero I.zero;
    value to_string prog_lang x =
      let sa = Q.to_string x.a in
      let sr =
        if I.eq (Q.rnum x.b) I.zero then ""
        else if I.lt x.d I.zero then
          if I.eq x.d I.minus_one then "i"
          else if prog_lang then sprintf "i*sqrt(%s)" (I.ts (I.neg x.d))
          else sprintf "i√%s" (I.ts (I.neg x.d))
        else
          sprintf "√%s" (I.ts x.d)
      in
      let sd =
        if I.eq x.b.Q.rden I.one then ""
        else sprintf "/%s" (I.ts x.b.Q.rden)
      in
      if I.eq x.a.Q.rnum I.zero then
        match I.ts x.b.Q.rnum with
        [ "1" → sprintf "%s%s" sr sd
        | "-1" → sprintf "-%s%s" sr sd
        | s → sprintf "%s%s%s" s sr sd ]
      else
        match I.ts x.b.Q.rnum with
        [ "0" → sa
        | "1" →
            if I.eq (Q.rden x.a) (Q.rden x.b) then
              sprintf "(%s+%s)%s" (I.ts (Q.rnum x.a)) sr sd
            else
              sprintf "(%s+%s%s)" sa sr sd
        | "-1" →
            if I.eq (Q.rden x.a) (Q.rden x.b) then
              sprintf "(%s-%s)%s" (I.ts (Q.rnum x.a)) sr sd
            else
              sprintf "(%s-%s%s)" sa sr sd
        | s →
            if I.lt (Q.rnum x.b) I.zero then
              if I.eq (Q.rden x.a) (Q.rden x.b) then
                sprintf "(%s%s%s)%s" (I.ts (Q.rnum x.a))
                  (I.ts (Q.rnum x.b)) sr sd
              else
                sprintf "(%s%s%s%s)" sa s sr sd
            else
              if I.eq (Q.rden x.a) (Q.rden x.b) then
                sprintf "(%s+%s%s)%s" (I.ts (Q.rnum x.a))
                  (I.ts (Q.rnum x.b)) sr sd
              else
                sprintf "(%s+%s%s%s)" sa s sr sd ]
    ;
    value of_i i = {a = Q.of_i i; b = Q.zero; d = I.zero};
    value of_q r = {a = r; b = Q.zero; d = I.zero};
    value to_q x =
      if I.eq x.d I.zero then Some x.a
      else None
    ;
    value norm x =
      let (i, s) = find_sqrt (I.abs x.d) in
      (* d = ε(d)*is² *)
      if I.eq i I.one && I.ge x.d I.zero then
        let a = Q.norm (Q.add x.a (Q.muli x.b s)) in
        let b = Q.zero in
        let d = I.zero in
        {a = a; b = b; d = d}
      else
        let a = Q.norm x.a in
        let b = Q.norm (Q.muli x.b s) in
        let d = if I.lt x.d I.zero then I.neg i else i in
        let b = if I.eq d I.zero then Q.zero else b in
        let d = if I.eq (Q.rnum b) I.zero then I.zero else d in
        {a = a; b = b; d = d}
    ;
    value neg a = make (Q.neg a.a) (Q.neg a.b) a.d;
    value add a₁ a₂ =
      if I.eq a₁.d a₂.d then
        let a = Q.norm (Q.add a₁.a a₂.a) in
        let b = Q.norm (Q.add a₁.b a₂.b) in
        if Q.eq b Q.zero then {a = a; b = b; d = I.zero}
        else {a = a; b = b; d = a₁.d}
      else if I.eq a₁.d I.zero then {(a₂) with a = Q.add a₁.a a₂.a}
      else if I.eq a₂.d I.zero then {(a₁) with a = Q.norm (Q.add a₁.a a₂.a)}
      else if a₁.d < a₂.d then failwith "A₂.add 1"
      else failwith "A₂.add 2"
    ;
    value addi a i = {(a) with a = Q.addi a.a i};
    value addq a q = {(a) with a = Q.add a.a q};
    value sub x y = add x (neg y);
    value muli a i = {(a) with a = Q.muli a.a i; b = Q.muli a.b i};
    value mulq a q = {(a) with a = Q.mul a.a q; b = Q.mul a.b q};
    value mul x y =
      if I.eq x.d I.zero then mulq y x.a
      else if I.eq y.d I.zero then mulq x y.a
      else if I.eq x.d y.d then
        let a = Q.add (Q.mul x.a y.a) (Q.muli (Q.mul x.b y.b) x.d) in
        let b = Q.add (Q.mul x.a y.b) (Q.mul x.b y.a) in
        if Q.eq b Q.zero then {a = a; b = b; d = I.zero}
        else {a = a; b = b; d = x.d}
      else if I.eq x.a.Q.rnum I.zero && I.eq y.a.Q.rnum I.zero then
        norm {a = Q.zero; b = Q.mul x.b y.b; d = I.mul x.d y.d}
      else
        failwith
          (sprintf "A₂.mul : à voir (%s)(%s)" (to_string False x)
             (to_string False y))
    ;
    value div x y =
      if I.eq x.d y.d then
        let den = Q.sub (Q.mul y.a y.a) (Q.muli (Q.mul y.b y.b) y.d) in
        let aa = Q.sub (Q.mul x.a y.a) (Q.muli (Q.mul x.b y.b) y.d) in
        let ab = Q.sub (Q.mul y.a x.b) (Q.mul x.a y.b) in
        norm {a = Q.div aa den; b = Q.div ab den; d = y.d}
      else if I.eq x.d I.zero then
        let den = Q.sub (Q.mul y.a y.a) (Q.muli (Q.mul y.b y.b) y.d) in
        let aa = Q.mul x.a y.a in
        let ab = Q.neg (Q.mul x.a y.b) in
        norm {a = Q.div aa den; b = Q.div ab den; d = y.d}
      else if I.eq y.d I.zero then
        norm {a = Q.div x.a y.a; b = Q.div x.b y.a; d = x.d}
      else
        failwith "not impl A₂.div"
    ;
    value divi x i =
      {a = Q.make x.a.Q.rnum (I.mul x.a.Q.rden i);
       b = Q.make x.b.Q.rnum (I.mul x.b.Q.rden i);
       d = x.d}
    ;
    value eq x y = Q.eq x.a y.a && Q.eq x.b y.b && I.eq x.d y.d;
    value gcd x y =
      if eq x zero then y
      else if eq y zero then x
      else if I.eq x.d y.d then
        if I.eq (Q.rden x.a) (Q.rden x.b) && I.eq (Q.rden y.a) (Q.rden y.b)
        then
          let gx = I.gcd (Q.rnum x.a) (Q.rnum x.b) in
          let xa = I.div (Q.rnum x.a) gx in
          let xb = I.div (Q.rnum x.b) gx in
          let gy = I.gcd (Q.rnum y.a) (Q.rnum y.b) in
          let ya = I.div (Q.rnum y.a) gy in
          let yb = I.div (Q.rnum y.b) gy in
          if I.eq xa ya && I.eq xb yb then
            {a = Q.of_i xa; b = Q.of_i xb; d = x.d}
          else one
        else one
      else one
    ;
    value to_float x =
      if I.lt x.d I.zero then invalid_arg "A₂.to_float"
      else Q.to_float x.a +. Q.to_float x.b *. sqrt (I.to_float x.d)
    ;
    value to_complex x =
      if I.lt x.d I.zero then
        let re = Q.to_float x.a in
        let im = Q.to_float x.b *. sqrt (-. I.to_float x.d) in
        {re = re; im = im}
      else
        let re = Q.to_float x.a +. Q.to_float x.b *. sqrt (I.to_float x.d) in
        {re = re; im = 0.}
    ;
    value rec of_expr =
      fun
      [ << - $a$ >> →
          match of_expr a with
          [ Some a → Some {(a) with a = Q.neg a.a; b = Q.neg a.b}
          | None → None ]
      | << $int:a$ >> →
          let a = make (Q.of_i (I.os a)) Q.zero I.zero in
          Some a
      | << $int:n$ / $int:d$ >> →
          let a =
            make (Q.make (I.os n) (I.os d)) Q.zero I.zero
          in
          Some a
      | << $int:d$ ** (1/2) >> →
          of_expr << 0 + 1 * ($int:d$ ** (1/2)) / 1 >>
      | << ($int:d$ ** (1/2)) / $int:bd$ >> →
          of_expr << 0 + 1 * ($int:d$ ** (1/2)) / $int:bd$ >>
      | << $int:bn$ * ($int:d$ ** (1/2)) / $int:bd$ >> →
          of_expr << 0 + $int:bn$ * ($int:d$ ** (1/2)) / $int:bd$ >>
      | << $a$ + $int:d$ ** (1/2) / $int:bd$ >> →
          of_expr << $a$ + 1 * ($int:d$ ** (1/2)) / $int:bd$ >>
      | << $a$ + $int:bn$ * ($int:d$ ** (1/2)) / $int:bd$ >> →
          match Q.of_expr_if_any a with
          [ Some a →
              let a = make a (Q.make (I.os bn) (I.os bd)) (I.os d) in
              Some a
          | None → failwith "1 A₂.of_expr" ]
      | << $flo:_$ >> → None
      | << $e₁$ + $e₂$ >> → not_impl "A₂.of_expr e₂ " e₂
      | << $lid:s$ $_$ $_$ >> → failwith (sprintf "A₂.of_expr lid %s" s)
      | a → not_impl "2 A₂.of_expr" a ]
    ;
    value to_expr a =
      let bn = a.b.Q.rnum in
      let bd = a.b.Q.rden in
      if I.eq a.a.Q.rnum I.zero then
        if I.eq bn I.zero then << 0 >>
        else if I.eq bn I.one then
          if I.eq bd I.one then << ($int:I.ts a.d$ ** (1/2)) >>
          else << ($int:I.ts a.d$ ** (1/2)) / $int:I.ts bd$ >>
        else << $int:I.ts bn$ * ($int:I.ts a.d$ ** (1/2)) / $int:I.ts bd$ >>
      else if I.eq a.b.Q.rnum I.zero then
        Q.to_expr a.a
      else
        let sr = << $int:I.ts a.d$ ** (1/2) >> in
        if I.eq bn I.one then << $Q.to_expr a.a$ + $sr$ / $int:I.ts bd$ >>
        else << $Q.to_expr a.a$ + $int:I.ts bn$ * $sr$ / $int:I.ts bd$ >>
    ;
  end;

module type Float =
  sig
    type t = α;
    value abs : t → t;
    value neg : t → t;
    value add : t → t → t;
    value sub : t → t → t;
    value mul : t → t → t;
    value div : t → t → t;
    value sqrt : t → t;
    value zero : t;
    value epsilon : t;
    value compare : t → t → int;
    value to_string : t → string;
    value of_string : string → t;
    value a₂_to_complex : A₂.t → complex t;
    value complex_nth_root : complex t → int → complex t;
    value cpoly_roots : list (complex t) → list (complex t);
  end;

module C_func (F : Float) =
  struct
    type t =
      [ Nalg of A₂.t
      | Ncpl of complex F.t ]
    ;
    type i = I.t;
    type q = Q.t;
    type a₂ = A₂.t;
    value zero = Nalg (A₂.zero);
    value one = Nalg (A₂.one);
    value minus_one = Nalg (A₂.minus_one);
    value of_i i = Nalg (A₂.of_i i);
    value of_q q = Nalg (A₂.of_q q);
    value of_a a = Nalg a;
    value check =
      fun
      [ Nalg x → A₂.check x
      | Ncpl c → () ]
    ;
    value to_complex =
      fun
      [ Nalg x → F.a₂_to_complex x
      | Ncpl c → c ]
    ;
    value normalise =
      fun
      [ Nalg x → Nalg (A₂.norm x)
      | Ncpl c → Ncpl c ]
    ;
    value nth_root c n =
      match c with
      [ Nalg x → failwith "C_func.nth_root Nalg x not impl"
      | Ncpl c → Ncpl (F.complex_nth_root c n) ]
    ;
    value neg =
      fun
      [ Nalg x → Nalg (A₂.neg x)
      | Ncpl c → Ncpl {re = F.neg c.re; im = F.neg c.im} ]
    ;
    value map_complex f x y = {re = f x.re y.re; im = f x.im y.im};
    value add x y =
      match (x, y) with
      [ (Nalg x, Nalg y) → Nalg (A₂.add x y)
      | _ → Ncpl (map_complex F.add (to_complex x) (to_complex y)) ]
    ;
    value sub x y =
      match (x, y) with
      [ (Nalg x, Nalg y) → Nalg (A₂.sub x y)
      | _ → Ncpl (map_complex F.sub (to_complex x) (to_complex y)) ]
    ;
    value complex_mul c d =
      {re = F.sub (F.mul c.re d.re) (F.mul c.im d.im);
       im = F.add (F.mul c.re d.im) (F.mul c.im d.re)}
    ;
    value mul x y =
      match (x, y) with
      [ (Nalg x, Nalg y) → Nalg (A₂.mul x y)
      | _ → Ncpl (complex_mul (to_complex x) (to_complex y)) ]
    ;
    value muli x i = mul x (Nalg (A₂.of_i i));
    value mulq x q = mul x (Nalg (A₂.of_q q));
    value mula x a = mul x (Nalg a);
    value compare x y =
      match (x, y) with
      [ (Nalg x, Nalg y) → compare x y
      | _ →
          let x = to_complex x in
          let y = to_complex y in
          let r = F.compare x.re y.re in
          if r = 0 then F.compare x.im y.im else r ]
    ;
    value complex_div x y =
      if F.compare (F.abs y.re) (F.abs y.im) ≥ 0 then
        let r = F.div y.im y.re in
        let d = F.add y.re (F.mul r y.im) in
        { re = F.div (F.add x.re (F.mul r x.im)) d;
          im = F.div (F.sub x.im (F.mul r x.re)) d }
      else
        let r = F.div y.re y.im in
        let d = F.add y.im (F.mul r y.re) in
        { re = F.div (F.add (F.mul r x.re) x.im) d;
          im = F.div (F.sub (F.mul r x.im) x.re) d }
    ;
    value div x y =
      match (x, y) with
      [ (Nalg x, Nalg y) → Nalg (A₂.div x y)
      | _ → Ncpl (complex_div (to_complex x) (to_complex y)) ]
    ;
    value complex_to_string prog_lang c =
      let m = if prog_lang then "*" else "" in
      let s = {re = F.to_string c.re; im = F.to_string c.im} in
      if F.compare c.im F.zero = 0 then
        if F.compare c.re F.zero < 0 then sprintf "(%s)" s.re else s.re
      else if F.compare c.re F.zero = 0 then
        if F.compare c.im F.zero < 0 then sprintf "(%s%si)" s.im m
        else sprintf "%s%si" s.im m
      else if F.compare c.im F.zero < 0 then
        sprintf "(%s%s%si)" s.re s.im m
      else
        sprintf "(%s+%s%si)" s.re s.im m
    ;
    value to_string prog_lang =
      fun
      [ Nalg x → A₂.to_string prog_lang x
      | Ncpl c → complex_to_string prog_lang c ]
    ;
    value gcd x y =
      match (x, y) with
      [ (Nalg x, Nalg y) → Nalg (A₂.gcd x y)
      | _ → Nalg (A₂.one) ]
    ;
    value eq x y =
      match (x, y) with
      [ (Nalg x, Nalg y) → A₂.eq x y
      | _ →
           let x = to_complex x in
           let y = to_complex y in
           F.compare x.re y.re = 0 && F.compare x.im y.im = 0 ]
    ;
    value neg_factor x =
      match x with
      [ Nalg a →
          if Q.is_neg a.A₂.a then
            if I.eq a.A₂.d I.zero then Some (neg x)
            else if Q.is_neg a.A₂.b then Some (neg x)
            else None
          else if Q.eq a.A₂.a Q.zero then
            if Q.is_neg a.A₂.b then Some (neg x)
            else None
          else None
      | Ncpl _ →
          let c = to_complex x in
          if F.compare c.re F.zero < 0 && F.compare c.im F.zero = 0 then
            Some (neg x)
          else
            None ]
    ;
    value sof = F.to_string;
    value to_expr =
      fun
      [ Nalg x → A₂.to_expr x
      | Ncpl {re = re; im = im} →
          if F.compare im F.zero = 0 then << $flo:sof re$ >>
          else << $flo:sof re$ + i * $flo:sof im$ >> ]
    ;
    value to_a =
      fun
      [ Nalg x → Some x
      | Ncpl c → None ]
    ;
    value to_q =
      fun
      [ Nalg x → A₂.to_q x
      | Ncpl c → None ]
    ;
   value of_expr =
      fun
      [ << $flo:re$ >> →
          Ncpl {re = F.of_string re; im = F.zero}
      | << $flo:re$ + i * $flo:im$ >> →
          Ncpl {re = F.of_string re; im = F.of_string im}
      | e →
          match A₂.of_expr e with
          [ Some a → Nalg a
          | None → not_impl "N.of_expr" e ] ]
    ;
    value of_float_string s = Ncpl {re = F.of_string s; im = F.zero};
    value of_complex c = Ncpl c;
    value eps = F.sqrt F.epsilon;
    value complex_round_zero r =
      let re = if F.compare (F.abs r.re) eps ≤ 0 then F.zero else r.re in
      let im = if F.compare (F.abs r.im) eps ≤ 0 then F.zero else r.im in
      {re = re; im = im}
    ;
    value float_round_zero =
      fun
      [ Nalg x → Nalg x
      | Ncpl c → Ncpl (complex_round_zero c) ]
    ;
    value complex_nth_root = F.complex_nth_root;
    value cpoly_roots = F.cpoly_roots;
  end;

module C =
  C_func
    (struct
       type t = float;
       value abs = abs_float;
       value neg = \~-.;
       value add = \+.;
       value sub = \-.;
       value mul = \*.;
       value div = \/.;
       value sqrt = sqrt;
       value zero = 0.0;
       value epsilon = epsilon_float;
       value compare = compare;
       value to_string = string_of_float;
       value of_string = float_of_string;
       value a₂_to_complex = A₂.to_complex;
       value complex_norm x =
         let r = abs_float x.re in
         let i = abs_float x.im in
         if r = 0.0 then i
         else if i = 0.0 then r
         else if r >= i then
           let q = i /. r in
           r *. sqrt (1.0 +. q *. q)
         else
           let q = r /. i in
           i *. sqrt (1.0 +. q *. q)
       ;
       value complex_polar n a = { re = cos a *. n; im = sin a *. n };
       value complex_nth_root x n =
         let arg = atan2 x.im x.re in
         let norm = complex_norm x in
         complex_polar (norm ** (1. /. float n)) (arg /. float n)
       ;
       value cpoly_roots = Cpoly.roots;
     end)
;

module M =
  C_func
    (struct
       open Cpoly;
       type t = Mfl.t;
       value abs = Mfl.abs;
       value neg = Mfl.neg;
       value add = Mfl.add;
       value sub = Mfl.sub;
       value mul = Mfl.mul;
       value div = Mfl.div;
       value sqrt = Mfl.sqrt;
       value power = Mfl.pow;
       value sin = Mfl.sin;
       value cos = Mfl.cos;
       value atan2 = Mfl.atan2;
       value zero = Mfl.float 0.0;
       value one = Mfl.float 1.0;
       value epsilon = Mfl.float epsilon_float;
       value compare x y = compare (Mfl.to_float x) (Mfl.to_float y);
       value eq x y = compare x y = 0;
       value ge x y = compare x y ≥ 0;
       value remove_trailing_zeros s =
         let len =
           loop (String.length s - 1) where rec loop i =
             if i < 0 then 0
             else if s.[i] = '0' then loop (i - 1)
             else i + 1
         in
         String.sub s 0 len
       ;
       value to_string f =
         let (s, e) = Mfl.to_nice_string 10 12 f in
         let (sign, s) =
           if s.[0] = '-' then ("-", String.sub s 1 (String.length s - 1))
           else ("", s)
         in      
         let s = remove_trailing_zeros s in
         if e = 0 then
           sprintf "%s0.%s" sign s
         else if e = 1 then
           let i = s.[0] in
           let d = String.sub s 1 (String.length s - 1) in
           let d = if d = "" then "0" else d in
           sprintf "%c.%s" i d
         else
           sprintf "%s.%sE%+03d" sign s e
       ;
       value of_string = Mfl.of_string;
       value a₂_to_complex a =
         let c = A₂.to_complex a in
         {re = Mfl.float c.re; im = Mfl.float c.im}
       ;
       value complex_norm x =
         let r = abs x.re in
         let i = abs x.im in
         if eq r zero then i
         else if eq i zero then r
         else if ge r i then
           let q = div i r in
           mul r (sqrt (add one (mul q q)))
         else
           let q = div r i in
           mul i (sqrt (add one (mul q q)))
       ;
       value complex_polar n a = { re = mul (cos a) n; im = mul (sin a) n };
       value complex_nth_root x n =
         let arg = atan2 x.im x.re in
         let norm = complex_norm x in
         complex_polar (power norm (div one (Mfl.float (float n))))
           (div arg (Mfl.float (float n)))
       ;
       value cpoly_roots = Cpoly.mroots;
     end)
;

value factor a =
  if I.lt a I.zero then invalid_arg "factor"
  else
    loop (I.of_int 2) a where rec loop b a =
      if I.gt b a then []
      else if I.eq (I.modn a b) I.zero then [b :: loop b (I.div a b)]
      else loop (I.succ b) a
;
