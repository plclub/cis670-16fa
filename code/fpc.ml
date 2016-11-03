(* Definitions with equi-recursive types in OCaml *)

(* --- Defining natural numbers with recursive types ----- *)

type ('a, 'b) sum = Inl of 'a | Inr of 'b

type 'a natF = (unit, 'a) sum

(* recursive type! *)

type nat = Fold of nat natF

let unfold (Fold x) = x

let (z : nat) = Fold (Inl ())
let s : nat -> nat = fun v -> Fold (Inr v)

let natF_map : ('a -> 'b) -> 'a natF -> 'b natF =
  fun f x -> match x with
     | Inl () -> Inl ()
     | Inr y  -> Inr (f y)

let rec nat_fold : ('a natF -> 'a) -> nat -> 'a =
  fun alg x ->
     alg (natF_map (nat_fold alg) (unfold x))

let rec nat_gen : ('a -> 'a natF) -> 'a -> nat =
  fun alg x ->
     Fold (natF_map (nat_gen alg) (alg x))

let add (x:nat) (y:nat) : nat =
  nat_fold (fun z -> match z with
                     | Inl () -> x
                     | Inr y' -> s y') y

let pred (x:nat) : nat = match (unfold x) with
   | Inl () -> x
   | Inr y  -> y

let rec omega = Fold (Inr omega)

let pred_omega = pred omega


(* ---- Defining fix with recursive types ----- *)

type 'a self = Self of ('a self -> 'a)

let unroll (Self x) = x

let fix : ('a -> 'a) -> 'a
   = fun f ->
   let d : 'a self -> 'a = fun x -> f (fun v -> unroll x x v) in
   d (Self d)


let add' (x : nat) : nat -> nat =
   fix (fun f -> (fun y -> match (unfold y) with
                        | Inl () -> x
                        | Inr y' -> (s (f y'))))

(* ---- Defining state with recursive types ----- *)

type signal = (bool * bool)  (* Inputs r & s *)

type rsl = { q' : bool ;  (* inverse of q  *)
             q  : bool ;  (* state of latch *)
             n  : signal -> rsl }

let hold  = (false, false)
let set   = (false, true)
let reset = (true, false)

let nor p q = not (p || q)

let rec rsl l (r,s) =
  let rec this = { q' = nor l.q s  ;
                   q  = nor r l.q' ;
                   n  = fun s -> rsl this s } in
  this

let rec init : rsl =
   { q' = false; q = false; n = fun s -> rsl init s }






