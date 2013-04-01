(* $Id: cpoly.ml,v 1.3 2013-04-01 05:30:15 deraugla Exp $ *)
(*
    ALGORITHM 419 COLLECTED ALGORITHMS FROM ACM.
    ALGORITHM APPEARED IN COMM. ACM, VOL. 15, NO. 02,
    P. 097.

  Added changes from Remark on Algorithm 419 by David H. Withers
  CACM (March 1974) Vol 17 No 3 p. 157 

  Translated into OCaml by D. de Rauglaudre (March 2013).
*)

open Printf;

type choice α β =
  [ Left of α
  | Right of β ]
;

module type Mfl =
  sig
    type t = α;
    value abs : t → t;
    value neg : t → t;
    value add : t → t → t;
    value sub : t → t → t;
    value mul : t → t → t;
    value div : t → t → t;
    value pow : t → t → t;
    value sqrt : t → t;
    value exp : t → t;
    value log : t → t;
    value min : t → t → t;
    value max : t → t → t;
    value cmp : t → t → int;
    value eq : t → t → bool;
    value neq : t → t → bool;
    value lt : t → t → bool;
    value le : t → t → bool;
    value gt : t → t → bool;
    value ge : t → t → bool;
    value int : int → t;
    value float : float → t;
    value zero : t;
    value one : t;
    value two : t;
    value set_prec : int → unit;
    value get_prec : t → int;
    value epsilon_float : int → t;
    value max_float : unit → t;
    value min_float : unit → t;
    value to_string : t → string;
    value to_float : t → float;
    value of_string : string → t;
  end;

module Mfl_mpfr : Mfl =
  struct
    type t = Mpfr.t;
    value abs = Mpfr.abs;
    value neg = Mpfr.neg;
    value add = Mpfr.add;
    value sub = Mpfr.sub;
    value mul = Mpfr.mul;
    value div = Mpfr.div;
    value pow = Mpfr.pow;
    value sqrt = Mpfr.sqrt;
    value exp = Mpfr.exp;
    value log = Mpfr.log;
    value cmp = Mpfr.cmp;
    value eq x y = cmp x y = 0;
    value neq x y = cmp x y <> 0;
    value lt x y = cmp x y < 0;
    value le x y = cmp x y ≤ 0;
    value gt x y = cmp x y > 0;
    value ge x y = cmp x y ≥ 0;
    value min x y = if lt x y then x else y;
    value max x y = if lt x y then y else x;
    value int i = Mpfr.of_float (float i);
    value float = Mpfr.of_float;
    value zero = Mpfr.of_float 0.0;
    value one = Mpfr.of_float 1.0;
    value two = Mpfr.of_float 2.0;
    value set_prec = Mpfr.set_default_prec;
    value get_prec = Mpfr.get_prec;
    value epsilon_float prec = pow two (sub one (int prec));
    value max_float () = float max_float;
    value min_float () = float min_float;
    value to_string f =
      let (s, e) = Mpfr.to_string 10 16 f in
      let (sign, s) =
        if s.[0] = '-' then ("-", String.sub s 1 (String.length s - 1))
        else (" ", s)
      in
      sprintf "%5s.%sE%+03d" sign s e
    ;
    value to_float = Mpfr.to_float;
    value of_string = Mpfr.of_string 10;
  end;

module Mfl_float : Mfl =
  struct
    type t = float;
    value abs = abs_float;
    value neg x = -. x;
    value add x y = x +. y;
    value sub x y = x -. y;
    value mul x y = x *. y;
    value div x y = x /. y;
    value pow x y = x ** y;
    value sqrt = sqrt;
    value exp = exp;
    value log = log;
    value min = min;
    value max = max;
    value cmp = compare;
    value eq x y = x = y;
    value neq x y = x <> y;
    value lt x y = x < y;
    value le x y = x ≤ y;
    value gt x y = x > y;
    value ge x y = x ≥ y;
    value int = float;
    value float x = x;
    value zero = 0.0;
    value one = 1.0;
    value two = 2.0;
    value set_prec _ = ();
    value get_prec _ = 53;
    value epsilon_float _ = epsilon_float;
    value max_float () = max_float;
    value min_float () = min_float;
    value to_string f = sprintf "%26.16E" f;
    value to_float f = f;
    value of_string = float_of_string;
  end;

module Mfl = Mfl_mpfr;

value \~-. = Mfl.neg;
value \+. = Mfl.add;
value \-. = Mfl.sub;
value \*. = Mfl.mul;
value \/. = Mfl.div;
value \** = Mfl.pow;
value abs_float = Mfl.abs;
value sqrt = Mfl.sqrt;
value exp = Mfl.exp;
value log = Mfl.log;
value max = Mfl.max;
value epsilon_float = Mfl.epsilon_float;
value max_float = Mfl.max_float;
value min_float = Mfl.min_float;

type complex α = { re : α; im : α };

value complex_neg x = {re = Mfl.neg x.re; im = Mfl.neg x.im};
value complex_zero = {re = Mfl.zero; im = Mfl.zero};
value complex_add x y = {re = Mfl.add x.re y.re; im = Mfl.add x.im y.im};
value complex_sub x y = {re = Mfl.sub x.re y.re; im = Mfl.sub x.im y.im};
value complex_eq x y = Mfl.eq x.re y.re && Mfl.eq x.im y.im;
value complex_neq x y = Mfl.neq x.re y.re || Mfl.neq x.im y.im;
value map_complex f x = {re = f x.re; im = f x.im};

type comm α =
  { p : array (complex α); h : array (complex α);
    qp : array (complex α); qh : array (complex α);
    sh : array (complex α);
    are : α; mre : α;
    eta : α; infin : α }
;

(* MODULUS OF A COMPLEX NUMBER AVOIDING OVERFLOW. *)
value cmod x =
  let ar = abs_float x.re in
  let ai = abs_float x.im in
  if Mfl.lt ar ai then ai *. sqrt (Mfl.one +. (ar/.ai) ** Mfl.two)
  else if Mfl.gt ar ai then ar *. sqrt (Mfl.one +. (ai/.ar) ** Mfl.two)
  else ar *. sqrt Mfl.two
;

(*
  RETURNS A SCALE FACTOR TO MULTIPLY THE COEFFICIENTS OF THE
  POLYNOMIAL. THE SCALING IS DONE TO AVOID OVERFLOW AND TO AVOID
  UNDETECTED UNDERFLOW INTERFERING WITH THE CONVERGENCE
  CRITERION.  THE FACTOR IS A POWER OF THE BASE.
  PT - MODULUS OF COEFFICIENTS OF P
  ETA,INFIN,SMALNO,BASE - CONSTANTS DESCRIBING THE
  FLOATING POINT ARITHMETIC.
*)
value scale comm smalno base nn =
  (* FIND LARGEST AND SMALLEST MODULI OF COEFFICIENTS. *)
  let hi = sqrt comm.infin in
  let lo = smalno /. comm.eta in
  let (min, max) =
    loop comm.infin Mfl.zero 0 where rec loop min max i =
      if i ≥ nn then (min, max)
      else
        let x = comm.sh.(i).re in
        let min = if Mfl.neq x Mfl.zero && Mfl.lt x min then x else min in
        let max = if Mfl.gt x max then x else max in
        loop min max (i + 1)
  in
  (* SCALE ONLY IF THERE ARE VERY LARGE OR VERY SMALL COMPONENTS. *)
  if Mfl.ge min lo && Mfl.le max hi then Mfl.one
  else
    let x = lo /. min in
    let sc =
      if Mfl.le x Mfl.one then Mfl.one /. sqrt max *. sqrt min
      else if Mfl.gt (comm.infin /. x) max then Mfl.one
      else x
    in
    let l = log sc /. log base +. Mfl.float 0.500 in
    base ** l
;

(* COMPLEX DIVISION C = A/B, AVOIDING OVERFLOW. *)
value cdivid comm a b =
  if Mfl.eq b.re Mfl.zero && Mfl.eq b.im Mfl.zero then
    (* DIVISION BY ZERO, C = INFINITY. *)
    {re = comm.infin; im = comm.infin}
  else if Mfl.lt (abs_float b.re) (abs_float b.im) then
    let r = b.re /. b.im in
    let d = b.im +. r *. b.re in
    {re = (a.re *. r +. a.im) /. d; im = (a.im *. r -. a.re) /. d}
  else
    let r = b.im /. b.re in
    let d = b.re +. r *. b.im in
    {re = (a.re +. a.im *. r) /. d; im = (a.im -. a.re *. r) /. d}
;

(*
  CAUCHY COMPUTES A LOWER BOUND ON THE MODULI OF THE ZEROS OF A
  POLYNOMIAL - PT IS THE MODULUS OF THE COEFFICIENTS.
*)
value cauchy nn p = do {
  let n = nn - 1 in
  p.(n) := {re = -. p.(n).re; im = p.(n).im};
  (* COMPUTE UPPER ESTIMATE OF BOUND. *)
  let x = exp ( (log (-. p.(n).re) -. log (p.(0).re)) /. Mfl.int n ) in
  let x =
    if Mfl.neq p.(n-1).re Mfl.zero then
      (* IF NEWTON STEP AT THE ORIGIN IS BETTER, USE IT. *)
      Mfl.min (-. p.(n).re /. p.(n-1).re) x
    else x
  in
  (* CHOP THE INTERVAL (0,X) UNITL F LE 0. *)
  let x =
    loop x Mfl.zero where rec loop x f =
      let xm = x *. Mfl.float 0.1 in
      let f =
        loop p.(0).re 1 where rec loop f i =
          if i > n then f
          else loop (f *. xm +. p.(i).re) (i + 1)
      in
      if Mfl.gt f Mfl.zero then loop xm f else x
  in
  (* DO NEWTON ITERATION UNTIL X CONVERGES TO TWO DECIMAL PLACES. *)
  loop 10 Mfl.zero x x where rec loop iter df dx x =
    if iter = 0 then failwith "cauchy not convergent"
    else if Mfl.gt (abs_float (dx /. x)) (Mfl.float 0.005) then do {
      p.(0) := {re = p.(0).re; im = p.(0).re};
      for i = 1 to n do {
        p.(i) := {re = p.(i).re; im = p.(i-1).im *. x +. p.(i).re};
      };
      let df =
        loop p.(0).im 1 where rec loop df i =
          if i ≥ n then df
          else loop (df *. x +. p.(i).im) (i + 1)
      in
      let dx = p.(n).im /. df in
      loop (iter - 1) df dx (x -. dx)
    }
    else x
};

(*
  COMPUTES  THE DERIVATIVE  POLYNOMIAL AS THE INITIAL H
  POLYNOMIAL AND COMPUTES L1 NO-SHIFT H POLYNOMIALS.
*)
value noshft comm l1 nn = do {
  let n = nn - 1 in
  let nm1 = n - 1 in
  for i = 0 to n - 1 do {
    let xni = Mfl.int (nn - i - 1) in
    comm.h.(i) :=
      {re = xni *. comm.p.(i).re /. Mfl.int n;
       im = xni *. comm.p.(i).im /. Mfl.int n};
  };
  for jj = 1 to l1 do {
    if Mfl.gt (cmod comm.h.(n-1))
         (comm.eta *. Mfl.int 10 *. cmod comm.p.(n-1))
    then do {
      let c = cdivid comm (complex_neg comm.p.(nn-1)) comm.h.(n-1) in
      for i = 1 to nm1 do {
        let j = nn - i - 1 in
        let t = comm.h.(j-1) in
        comm.h.(j) :=
          {re = c.re *. t.re -. c.im *. t.im +. comm.p.(j).re;
           im = c.re *. t.im +. c.im *. t.re +. comm.p.(j).im};
      };
      comm.h.(0) := comm.p.(0);
    }
    else do {
      (* IF THE CONSTANT TERM IS ESSENTIALLY ZERO, SHIFT H COEFFICIENTS. *)
      for i = 1 to nm1 do {
         let j = nn - i - 1 in
         comm.h.(j) := comm.h.(j-1);
      };
      comm.h.(0) := complex_zero;
    };
  };
};

(*
  EVALUATES A POLYNOMIAL  P  AT  S  BY THE HORNER RECURRENCE
  PLACING THE PARTIAL SUMS IN Q AND THE COMPUTED VALUE IN PV.
*)
value polyev nn s p q = do {
  q.(0) := p.(0);
  loop q.(0) 1 where rec loop pv i =
    if i ≥ nn then pv
    else do {
      let pvr = pv.re *. s.re -. pv.im *. s.im +. p.(i).re in
      let pvi = pv.re *. s.im +. pv.im *. s.re +. p.(i).im in
      let pv = {re = pvr; im = pvi} in
      q.(i) := pv;
      loop pv (i + 1)
    }
};

(*
  COMPUTES  T = -P(S)/H(S).
  BOOL   - LOGICAL, SET TRUE IF H(S) IS ESSENTIALLY ZERO.
*)
value calct comm s pv nn =
  let n = nn - 1 in
  (* EVALUATE H(S). *)
  let hv = polyev n s comm.h comm.qh in
  if Mfl.le (cmod hv) (comm.are *. Mfl.float 10.0 *. cmod comm.h.(n-1)) then
    None
  else
    Some (cdivid comm (complex_neg pv) hv)
;

(*
  CALCULATES THE NEXT SHIFTED H POLYNOMIAL.
  BOOL   -  LOGICAL, IF .TRUE. H(S) IS ESSENTIALLY ZERO
*)
value nexth comm c_opt nn = do {
  let n = nn - 1 in
  match c_opt with
  [ Some c → do {
      for j = 1 to n - 1 do {
        let t = comm.qh.(j-1) in
        comm.h.(j) :=
          {re = c.re *. t.re -. c.im *. t.im +. comm.qp.(j).re;
           im = c.re *. t.im +. c.im *. t.re +. comm.qp.(j).im};
      };
      comm.h.(0) := comm.qp.(0);
    }
  | None → do {
      (* IF H(S) IS ZERO REPLACE H WITH QH. *)
      for j = 1 to n - 1 do { comm.h.(j) := comm.qh.(j-1) };
      comm.h.(0) := complex_zero;
    } ]
};

(*
  BOUNDS THE ERROR IN EVALUATING THE POLYNOMIAL BY THE HORNER
  RECURRENCE.
  QR,QI - THE PARTIAL SUMS
  MS    -MODULUS OF THE POINT
  MP    -MODULUS OF POLYNOMIAL VALUE
  ARE, MRE -ERROR BOUNDS ON COMPLEX ADDITION AND MULTIPLICATION
*)
value errev comm ms mp nn =
  let e = cmod comm.qp.(0) *. comm.mre /. (comm.are +. comm.mre) in
  loop e 0 where rec loop e i =
    if i ≥ nn then e *. (comm.are +. comm.mre) -. mp *. comm.mre
    else loop (e *. ms +. cmod comm.qp.(i)) (i + 1)
;

(*
  CARRIES OUT THE THIRD STAGE ITERATION.
  L3 - LIMIT OF STEPS IN STAGE 3.
  ZR,ZI   - ON ENTRY CONTAINS THE INITIAL ITERATE, IF THE
  ITERATION CONVERGES IT CONTAINS THE FINAL ITERATE
  ON EXIT.
  CONV    -  .TRUE. IF ITERATION CONVERGES
*)
value vrshft comm l3 pv z nn =
  (* MAIN LOOP FOR STAGE THREE *)
  loop pv z Mfl.zero Mfl.zero False 1 where rec loop pv s omp relstp b i =
    if i > l3 then (None, z)
    else do {
      (* EVALUATE P AT S AND TEST FOR CONVERGENCE. *)
      let pv = polyev nn s comm.p comm.qp in
      let mp = cmod pv in
      let ms = cmod s in
      let (s, pv, terminated) =
        if Mfl.le mp (Mfl.float 20.0 *. errev comm ms mp nn) then
          (* POLYNOMIAL VALUE IS SMALLER IN VALUE THAN A BOUND ON THE ERROR
             IN EVALUATING P, TERMINATE THE ITERATION. *)
          (s, pv, Right (True, s))
        else if i = 1 then
          (s, pv, Left (mp, b))
        else if not b && Mfl.ge mp omp && Mfl.lt relstp (Mfl.float 0.05)
        then do {
          (* ITERATION HAS STALLED. PROBABLY A CLUSTER OF ZEROS. DO 5
             FIXED SHIFT STEPS INTO THE CLUSTER TO FORCE ONE ZERO TO
             DOMINATE. *)
          let r = sqrt (max relstp comm.eta) in
          let rr = s.re *. (Mfl.one +. r) -. s.im *. r in
          let ri = s.re *. r +. s.im *. (Mfl.one +. r) in
          let s = {re = rr; im = ri} in
          let pv = polyev nn s comm.p comm.qp in
          for j = 1 to 5 do { nexth comm (calct comm s pv nn) nn };
          (s, pv, Left (comm.infin, True))
        }
        else
          (* EXIT IF POLYNOMIAL VALUE INCREASES SIGNIFICANTLY. *)
          let terminated =
            if Mfl.gt (mp *. Mfl.float 0.1) omp then
              Right (False, z)
            else
              Left (mp, b)
          in
          (s, pv, terminated)
      in
      match terminated with
      [ Right (conv, z) →
          let pv_opt = if conv then Some pv else None in
          (pv_opt, z)
      | Left (omp, b) → do {
          (* CALCULATE NEXT ITERATE. *)
          nexth comm (calct comm s pv nn) nn;
          let c_opt = calct comm s pv nn in
          let (s, relstp) =
            match c_opt with
            [ Some c → (complex_add s c, cmod c /. cmod s)
            | None → (s, relstp) ]
          in
          loop pv s omp relstp b (i + 1)
        } ]
    }
;

(*
  COMPUTES L2 FIXED-SHIFT H POLYNOMIALS AND TESTS FOR CONVERGENCE.
  INITIATES A VARIABLE-SHIFT ITERATION AND RETURNS WITH THE
  APPROXIMATE ZERO IF SUCCESSFUL.
  L2 - LIMIT OF FIXED SHIFT STEPS
  ZR,ZI - APPROXIMATE ZERO IF CONV IS .TRUE.
  CONV  - LOGICAL INDICATING CONVERGENCE OF STAGE 3 ITERATION
*)
value fxshft comm s l2 nn =
  let n = nn - 1 in
  (* EVALUATE P AT S. *)
  let pv = polyev nn s comm.p comm.qp in
  let (pv, z) =
    (* CALCULATE FIRST T = -P(S)/H(S). *)
    let c_opt = calct comm s pv nn in
    (* MAIN LOOP FOR ONE SECOND STAGE STEP. *)
    loop pv complex_zero False True c_opt 1
    where rec loop pv z pasd test c_opt j =
      if j > l2 then (pv, z)
      else do {
        let ot =
          match c_opt with
          [ Some c → c
          | None → complex_zero ]
        in
        (* COMPUTE NEXT H POLYNOMIAL AND NEW T. *)
        nexth comm c_opt nn;
        let c_opt = calct comm s pv nn in
        let z =
          match c_opt with
          [ Some c → complex_add s c
          | None → s ]
        in
        (* TEST FOR CONVERGENCE UNLESS STAGE 3 HAS FAILED ONCE OR THIS
           C IS THE LAST H POLYNOMIAL . *)
        match c_opt with
        [ Some c →
            if not test || j = l2 then
              loop pv z pasd test c_opt (j + 1)
            else if
              Mfl.ge (cmod (complex_sub c ot)) (Mfl.float 0.5 *. cmod z)
            then
              loop pv z False test c_opt (j + 1)
            else if not pasd then
              loop pv z True test c_opt (j + 1)
            else do {
              (* THE WEAK CONVERGENCE TEST HAS BEEN PASSED TWICE, START
                 THE THIRD STAGE ITERATION, AFTER SAVING THE CURRENT H
                 POLYNOMIAL AND SHIFT. *)
              for i = 0 to n - 1 do { comm.sh.(i) := comm.h.(i) };
              let (pv_opt, z) = vrshft comm 10 pv z nn in
              match pv_opt with
              [ Some pv → (pv, z)
              | None → do {
                  (* THE ITERATION FAILED TO CONVERGE. TURN OFF TESTING AND
                     RESTORE H,S,PV AND T. *)
                  for i = 0 to n - 1 do { comm.h.(i) := comm.sh.(i) };
                  let pv = polyev nn s comm.p comm.qp in
                  let c_opt = calct comm s pv nn in
                  loop pv z pasd False c_opt (j + 1)
                } ]
            }
        | None →
            loop pv z pasd test None (j + 1) ]
      }
  in
  (* ATTEMPT AN ITERATION WITH FINAL H POLYNOMIAL FROM SECOND STAGE. *)
  let (pv_opt, z) = vrshft comm 10 pv z nn in
  match pv_opt with
  [ Some _ → Some z
  | None → None ]
;

(*
  MCON PROVIDES MACHINE CONSTANTS USED IN VARIOUS PARTS OF THE
  PROGRAM. THE USER MAY EITHER SET THEM DIRECTLY OR USE THE
  STATEMENTS BELOW TO COMPUTE THEM. THE MEANING OF THE FOUR
  CONSTANTS ARE -
  ETA       THE MAXIMUM RELATIVE REPRESENTATION ERROR
  WHICH CAN BE DESCRIBED AS THE SMALLEST POSITIVE
  FLOATING-POINT NUMBER SUCH THAT 1.0D0 + ETA IS
  GREATER THAN 1.0D0.
  INFINY    THE LARGEST FLOATING-POINT NUMBER
  SMALNO    THE SMALLEST POSITIVE FLOATING-POINT NUMBER
  BASE      THE BASE OF THE FLOATING-POINT NUMBER SYSTEM USED
  LET T BE THE NUMBER OF BASE-DIGITS IN EACH FLOATING-POINT
  NUMBER(DOUBLE PRECISION). THEN ETA IS EITHER .5*B**(1-T)
  OR B**(1-T) DEPENDING ON WHETHER ROUNDING OR TRUNCATION
  IS USED.
  LET M BE THE LARGEST EXPONENT AND N THE SMALLEST EXPONENT
  IN THE NUMBER SYSTEM. THEN INFINY IS (1-BASE**(-T))*BASE**M
  AND SMALNO IS BASE**N.
  THE VALUES FOR BASE,T,M,N BELOW CORRESPOND TO THE IBM/360.
*)
value mcon prec =
  let eta = epsilon_float prec in
  let infiny = max_float () in
  let smalno = min_float () in
  let base = Mfl.two in
  (eta, infiny, smalno, base)
;

value pi = 3.1415926535897932384626;

(*
  Added changes from Remark on Algorithm 419 by David H. Withers
  CACM (March 1974) Vol 17 No 3 p. 157 

  FINDS THE ZEROS OF A COMPLEX POLYNOMIAL.
  OPR, OPI  -  DOUBLE PRECISION VECTORS OF REAL AND
  IMAGINARY PARTS OF THE COEFFICIENTS IN
  ORDER OF DECREASING POWERS.
  DEGREE    -  INTEGER DEGREE OF POLYNOMIAL.
  ZEROR, ZEROI  -  OUTPUT DOUBLE PRECISION VECTORS OF
  REAL AND IMAGINARY PARTS OF THE ZEROS.
  FAIL      -  OUTPUT LOGICAL PARAMETER,  TRUE  ONLY IF
  LEADING COEFFICIENT IS ZERO OR IF CPOLY
  HAS FOUND FEWER THAN DEGREE ZEROS.
  THE PROGRAM HAS BEEN WRITTEN TO REDUCE THE CHANCE OF OVERFLOW
  OCCURRING. IF IT DOES OCCUR, THERE IS STILL A POSSIBILITY THAT
  THE ZEROFINDER WILL WORK PROVIDED THE OVERFLOWED QUANTITY IS
  REPLACED BY A LARGE NUMBER.
*)
value cpoly op =
  let prec = Mfl.get_prec op.(0).re in
(*
  let _ = printf "prec %d\n%!" prec in
*)
  let degree = Array.length op - 1 in
  (* INITIALIZATION OF CONSTANTS *)
  let (eta, infin, smalno, base) = mcon prec in
  let mre = Mfl.two *. sqrt Mfl.two *. eta in
  let comm =
    {p = Array.make (degree + 1) complex_zero;
     h = Array.make (degree + 1) complex_zero;
     qp = Array.make (degree + 1) complex_zero;
     qh = Array.make (degree + 1) complex_zero;
     sh = Array.make (degree + 1) complex_zero;
     are = eta; mre = mre; eta = eta; infin = infin}
  in
  let zero = Array.make degree complex_zero in
  let xx = sqrt (Mfl.float 0.5) in
  let yy = -. xx in
  let fmul = Pervasives.\*. in
  let fdiv = Pervasives.\/. in
  let cosr = Mfl.float (cos (fmul (fdiv 94. 180.) pi)) in
  let sinr = Mfl.float (sin (fmul (fdiv 94. 180.) pi)) in
  (* ALGORITHM FAILS IF THE LEADING COEFFICIENT IS ZERO. *)
  if complex_eq op.(0) complex_zero then None
  else do {
    (* REMOVE THE ZEROS AT THE ORIGIN IF ANY. *)
    let nn =
      loop (degree + 1) where rec loop nn =
        if complex_neq op.(nn-1) complex_zero then nn
        else do {
          let idnn2 = degree - nn + 2 in
          zero.(idnn2-1) := complex_zero;
          loop (nn - 1)
        }
    in
    (* MAKE A COPY OF THE COEFFICIENTS. *)
    for i = 0 to nn - 1 do {
      comm.p.(i) := op.(i);
      comm.sh.(i) := {re = cmod comm.p.(i); im = Mfl.zero};
    };
    (* SCALE THE POLYNOMIAL. *)
    let bnd = scale comm smalno base nn in
    if Mfl.neq bnd Mfl.one then do {
      for i = 0 to nn - 1 do {
        comm.p.(i) := {re = bnd *. comm.p.(i).re; im = bnd *. comm.p.(i).im};
      }
    }
    else ();
    (* START THE ALGORITHM FOR ONE ZERO . *)
    loop40 xx yy nn where rec loop40 xx yy nn =
      if nn ≤ 2 then do {
        (* CALCULATE THE FINAL ZERO AND RETURN. *)
        let c = cdivid comm (complex_neg comm.p.(1)) comm.p.(0) in
        zero.(degree-1) := c;
        Some zero
      }
      else do {
        (* CALCULATE BND, A LOWER BOUND ON THE MODULUS OF THE ZEROS. *)
        for i = 0 to nn - 1 do {
          comm.sh.(i) := {re = cmod comm.p.(i); im = Mfl.zero};
        };
        let bnd = cauchy nn comm.sh in
        (* OUTER LOOP TO CONTROL 2 MAJOR PASSES WITH DIFFERENT SEQUENCES
           OF SHIFTS. *)
        loop100 xx yy 1 where rec loop100 xx yy cnt1 =
          if cnt1 > 2 then
            (* THE ZEROFINDER HAS FAILED ON TWO MAJOR PASSES.
               RETURN EMPTY HANDED. *)
            None
          else do {
            (* FIRST STAGE CALCULATION, NO SHIFT. *)
            noshft comm 5 nn;
            (* INNER LOOP TO SELECT A SHIFT. *)
            loop90 xx yy 1 where rec loop90 xx yy cnt2 =
              if cnt2 > 9 then
                (* IF 9 SHIFTS FAIL, THE OUTER LOOP IS REPEATED WITH ANOTHER
                   SEQUENCE OF SHIFTS. *)
                loop100 xx yy (cnt1 + 1)
              else
                (* SHIFT IS CHOSEN WITH MODULUS BND AND AMPLITUDE ROTATED BY
                   94 DEGREES FROM THE PREVIOUS SHIFT *)
                let xxx = cosr *. xx -. sinr *. yy in
                let yy = sinr *. xx +. cosr *. yy in
                let xx = xxx in
                let s = {re = bnd *. xx; im = bnd *. yy} in
                (* SECOND STAGE CALCULATION, FIXED SHIFT. *)
                match fxshft comm s (10*cnt2) nn with
                [ Some z → do {
                    (* THE SECOND STAGE JUMPS DIRECTLY TO THE THIRD STAGE
                       ITERATION. IF SUCCESSFUL THE ZERO IS STORED AND THE
                       POLYNOMIAL DEFLATED. *)
                    let idnn2 = degree - nn + 2 in
                    zero.(idnn2-1) := z;
                    for i = 0 to nn - 2 do { comm.p.(i) := comm.qp.(i) };
                    loop40 xx yy (nn - 1)
                  }
                | None →
                    (* IF THE ITERATION IS UNSUCCESSFUL ANOTHER SHIFT IS
                       CHOSEN. *)
                    loop90 xx yy (cnt2 + 1) ]
          }
      }
  }
;

value mroots p =
  if List.length p ≤ 1 then []
  else
    match cpoly (Array.of_list p) with
    [ Some z → Array.to_list z
    | None → failwith "Cpoly.mroots" ]
;

value roots p =
  if List.length p ≤ 1 then []
  else
    let p = List.map (map_complex Mfl.float) p in
    match cpoly (Array.of_list p) with
    [ Some z → List.map (map_complex Mfl.to_float) (Array.to_list z)
    | None → failwith "Cpoly.roots" ]
;

value froots p = roots (List.map (fun r → {re = r; im = 0.}) p);
value iroots p = roots (List.map (fun i → {re = float i; im = 0.}) p);
