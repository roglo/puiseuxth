(* $Id: series.ml,v 1.10 2013-08-07 01:12:11 deraugla Exp $ *)

#load "./pa_coq.cmo";

Record series α :=
  { terms : nat → α;
    stop : option nat }.

Definition series_nth α n (s : series α) :=
  match stop s with
  | Some st => if lt_dec n st then Some (terms s n) else None
  | None => None
  end.

CoInductive coseries α :=
  | Term : α → coseries α → coseries α
  | End : coseries α.

Definition coseries_hd α (s : coseries α) :=
  match s with
  | Term a _ => Some a
  | End => None
  end.

Definition coseries_tl α (s : coseries α) : option (coseries α) :=
  match s with
  | Term _ t => Some t
  | End => None
  end.

Fixpoint coseries_nth_tl α (n : nat) (s : coseries α) : option (coseries α) :=
  match n with
  | O => Some s
  | S m =>
      match coseries_tl s with
      | None => None
      | Some t => coseries_nth_tl m t
      end
  end.

Definition coseries_nth α (n : nat) (s : coseries α) : option α :=
  match coseries_nth_tl n s with
  | None => None
  | Some t => coseries_hd t
  end.

CoFixpoint coseries_map α β (f : α → β) s :=
  match s with
  | Term a t => Term (f a) (coseries_map f t)
  | End => End _
  end.

open Field;

value series_of_coseries fld (cs : coseries α) =
  {terms i =
     match coseries_nth i cs with
     | Some c → c
     | None → zero fld
     end;
   stop =
     loop 0 cs where rec loop i cs =
       if i = 60 then failwith "series_of_coseries None"
       else
         match cs with
         | Term _ cs' → loop (i + 1) (Lazy.force cs')
         | End → Some i
         end}
;

value coseries_of_series (s : series α) =
  let rec loop n =
    match series_nth n s with
    | Some t → Term t (loop (n + 1))
    | None → End
    end
  in
  loop 0
;

