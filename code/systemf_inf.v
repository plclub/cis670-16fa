Add LoadPath ".".
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export LibLNgen.

Require Export systemf_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme Typ_ind' := Induction for Typ Sort Prop.

Definition Typ_mutind :=
  fun H1 H2 H3 H4 H5 =>
  Typ_ind' H1 H2 H3 H4 H5.

Scheme Typ_rec' := Induction for Typ Sort Set.

Definition Typ_mutrec :=
  fun H1 H2 H3 H4 H5 =>
  Typ_rec' H1 H2 H3 H4 H5.

Scheme Exp_ind' := Induction for Exp Sort Prop.

Definition Exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  Exp_ind' H1 H2 H3 H4 H5 H6 H7.

Scheme Exp_rec' := Induction for Exp Sort Set.

Definition Exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  Exp_rec' H1 H2 H3 H4 H5 H6 H7.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_Typ_wrt_Typ_rec (n1 : nat) (typ1 : typ) (t1 : Typ) {struct t1} : Typ :=
  match t1 with
    | t_var_f typ2 => if (typ1 == typ2) then (t_var_b n1) else (t_var_f typ2)
    | t_var_b n2 => if (lt_ge_dec n2 n1) then (t_var_b n2) else (t_var_b (S n2))
    | t_arr t2 t3 => t_arr (close_Typ_wrt_Typ_rec n1 typ1 t2) (close_Typ_wrt_Typ_rec n1 typ1 t3)
    | t_all t2 => t_all (close_Typ_wrt_Typ_rec (S n1) typ1 t2)
  end.

Definition close_Typ_wrt_Typ typ1 t1 := close_Typ_wrt_Typ_rec 0 typ1 t1.

Fixpoint close_Exp_wrt_Exp_rec (n1 : nat) (x1 : x) (e1 : Exp) {struct e1} : Exp :=
  match e1 with
    | e_var_f x2 => if (x1 == x2) then (e_var_b n1) else (e_var_f x2)
    | e_var_b n2 => if (lt_ge_dec n2 n1) then (e_var_b n2) else (e_var_b (S n2))
    | e_lam t1 e2 => e_lam t1 (close_Exp_wrt_Exp_rec (S n1) x1 e2)
    | e_ap e2 e3 => e_ap (close_Exp_wrt_Exp_rec n1 x1 e2) (close_Exp_wrt_Exp_rec n1 x1 e3)
    | e_Lam e2 => e_Lam (close_Exp_wrt_Exp_rec n1 x1 e2)
    | e_App e2 t1 => e_App (close_Exp_wrt_Exp_rec n1 x1 e2) t1
  end.

Fixpoint close_Exp_wrt_Typ_rec (n1 : nat) (typ1 : typ) (e1 : Exp) {struct e1} : Exp :=
  match e1 with
    | e_var_f x1 => e_var_f x1
    | e_var_b n2 => e_var_b n2
    | e_lam t1 e2 => e_lam (close_Typ_wrt_Typ_rec n1 typ1 t1) (close_Exp_wrt_Typ_rec n1 typ1 e2)
    | e_ap e2 e3 => e_ap (close_Exp_wrt_Typ_rec n1 typ1 e2) (close_Exp_wrt_Typ_rec n1 typ1 e3)
    | e_Lam e2 => e_Lam (close_Exp_wrt_Typ_rec (S n1) typ1 e2)
    | e_App e2 t1 => e_App (close_Exp_wrt_Typ_rec n1 typ1 e2) (close_Typ_wrt_Typ_rec n1 typ1 t1)
  end.

Definition close_Exp_wrt_Exp x1 e1 := close_Exp_wrt_Exp_rec 0 x1 e1.

Definition close_Exp_wrt_Typ typ1 e1 := close_Exp_wrt_Typ_rec 0 typ1 e1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_Typ (t1 : Typ) {struct t1} : nat :=
  match t1 with
    | t_var_f typ1 => 1
    | t_var_b n1 => 1
    | t_arr t2 t3 => 1 + (size_Typ t2) + (size_Typ t3)
    | t_all t2 => 1 + (size_Typ t2)
  end.

Fixpoint size_Exp (e1 : Exp) {struct e1} : nat :=
  match e1 with
    | e_var_f x1 => 1
    | e_var_b n1 => 1
    | e_lam t1 e2 => 1 + (size_Typ t1) + (size_Exp e2)
    | e_ap e2 e3 => 1 + (size_Exp e2) + (size_Exp e3)
    | e_Lam e2 => 1 + (size_Exp e2)
    | e_App e2 t1 => 1 + (size_Exp e2) + (size_Typ t1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_Typ_wrt_Typ : nat -> Typ -> Prop :=
  | degree_wrt_Typ_t_var_f : forall n1 typ1,
    degree_Typ_wrt_Typ n1 (t_var_f typ1)
  | degree_wrt_Typ_t_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_Typ_wrt_Typ n1 (t_var_b n2)
  | degree_wrt_Typ_t_arr : forall n1 t1 t2,
    degree_Typ_wrt_Typ n1 t1 ->
    degree_Typ_wrt_Typ n1 t2 ->
    degree_Typ_wrt_Typ n1 (t_arr t1 t2)
  | degree_wrt_Typ_t_all : forall n1 t1,
    degree_Typ_wrt_Typ (S n1) t1 ->
    degree_Typ_wrt_Typ n1 (t_all t1).

Scheme degree_Typ_wrt_Typ_ind' := Induction for degree_Typ_wrt_Typ Sort Prop.

Definition degree_Typ_wrt_Typ_mutind :=
  fun H1 H2 H3 H4 H5 =>
  degree_Typ_wrt_Typ_ind' H1 H2 H3 H4 H5.

Hint Constructors degree_Typ_wrt_Typ : core lngen.

Inductive degree_Exp_wrt_Exp : nat -> Exp -> Prop :=
  | degree_wrt_Exp_e_var_f : forall n1 x1,
    degree_Exp_wrt_Exp n1 (e_var_f x1)
  | degree_wrt_Exp_e_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_Exp_wrt_Exp n1 (e_var_b n2)
  | degree_wrt_Exp_e_lam : forall n1 t1 e1,
    degree_Exp_wrt_Exp (S n1) e1 ->
    degree_Exp_wrt_Exp n1 (e_lam t1 e1)
  | degree_wrt_Exp_e_ap : forall n1 e1 e2,
    degree_Exp_wrt_Exp n1 e1 ->
    degree_Exp_wrt_Exp n1 e2 ->
    degree_Exp_wrt_Exp n1 (e_ap e1 e2)
  | degree_wrt_Exp_e_Lam : forall n1 e1,
    degree_Exp_wrt_Exp n1 e1 ->
    degree_Exp_wrt_Exp n1 (e_Lam e1)
  | degree_wrt_Exp_e_App : forall n1 e1 t1,
    degree_Exp_wrt_Exp n1 e1 ->
    degree_Exp_wrt_Exp n1 (e_App e1 t1).

Inductive degree_Exp_wrt_Typ : nat -> Exp -> Prop :=
  | degree_wrt_Typ_e_var_f : forall n1 x1,
    degree_Exp_wrt_Typ n1 (e_var_f x1)
  | degree_wrt_Typ_e_var_b : forall n1 n2,
    degree_Exp_wrt_Typ n1 (e_var_b n2)
  | degree_wrt_Typ_e_lam : forall n1 t1 e1,
    degree_Typ_wrt_Typ n1 t1 ->
    degree_Exp_wrt_Typ n1 e1 ->
    degree_Exp_wrt_Typ n1 (e_lam t1 e1)
  | degree_wrt_Typ_e_ap : forall n1 e1 e2,
    degree_Exp_wrt_Typ n1 e1 ->
    degree_Exp_wrt_Typ n1 e2 ->
    degree_Exp_wrt_Typ n1 (e_ap e1 e2)
  | degree_wrt_Typ_e_Lam : forall n1 e1,
    degree_Exp_wrt_Typ (S n1) e1 ->
    degree_Exp_wrt_Typ n1 (e_Lam e1)
  | degree_wrt_Typ_e_App : forall n1 e1 t1,
    degree_Exp_wrt_Typ n1 e1 ->
    degree_Typ_wrt_Typ n1 t1 ->
    degree_Exp_wrt_Typ n1 (e_App e1 t1).

Scheme degree_Exp_wrt_Exp_ind' := Induction for degree_Exp_wrt_Exp Sort Prop.

Definition degree_Exp_wrt_Exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  degree_Exp_wrt_Exp_ind' H1 H2 H3 H4 H5 H6 H7.

Scheme degree_Exp_wrt_Typ_ind' := Induction for degree_Exp_wrt_Typ Sort Prop.

Definition degree_Exp_wrt_Typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  degree_Exp_wrt_Typ_ind' H1 H2 H3 H4 H5 H6 H7.

Hint Constructors degree_Exp_wrt_Exp : core lngen.

Hint Constructors degree_Exp_wrt_Typ : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_Typ : Typ -> Set :=
  | lc_set_t_var_f : forall typ1,
    lc_set_Typ (t_var_f typ1)
  | lc_set_t_arr : forall t1 t2,
    lc_set_Typ t1 ->
    lc_set_Typ t2 ->
    lc_set_Typ (t_arr t1 t2)
  | lc_set_t_all : forall t1,
    (forall typ1 : typ, lc_set_Typ (open_Typ_wrt_Typ t1 (t_var_f typ1))) ->
    lc_set_Typ (t_all t1).

Scheme lc_Typ_ind' := Induction for lc_Typ Sort Prop.

Definition lc_Typ_mutind :=
  fun H1 H2 H3 H4 =>
  lc_Typ_ind' H1 H2 H3 H4.

Scheme lc_set_Typ_ind' := Induction for lc_set_Typ Sort Prop.

Definition lc_set_Typ_mutind :=
  fun H1 H2 H3 H4 =>
  lc_set_Typ_ind' H1 H2 H3 H4.

Scheme lc_set_Typ_rec' := Induction for lc_set_Typ Sort Set.

Definition lc_set_Typ_mutrec :=
  fun H1 H2 H3 H4 =>
  lc_set_Typ_rec' H1 H2 H3 H4.

Hint Constructors lc_Typ : core lngen.

Hint Constructors lc_set_Typ : core lngen.

Inductive lc_set_Exp : Exp -> Set :=
  | lc_set_e_var_f : forall x1,
    lc_set_Exp (e_var_f x1)
  | lc_set_e_lam : forall t1 e1,
    lc_set_Typ t1 ->
    (forall x1 : x, lc_set_Exp (open_Exp_wrt_Exp e1 (e_var_f x1))) ->
    lc_set_Exp (e_lam t1 e1)
  | lc_set_e_ap : forall e1 e2,
    lc_set_Exp e1 ->
    lc_set_Exp e2 ->
    lc_set_Exp (e_ap e1 e2)
  | lc_set_e_Lam : forall e1,
    (forall typ1 : typ, lc_set_Exp (open_Exp_wrt_Typ e1 (t_var_f typ1))) ->
    lc_set_Exp (e_Lam e1)
  | lc_set_e_App : forall e1 t1,
    lc_set_Exp e1 ->
    lc_set_Typ t1 ->
    lc_set_Exp (e_App e1 t1).

Scheme lc_Exp_ind' := Induction for lc_Exp Sort Prop.

Definition lc_Exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 =>
  lc_Exp_ind' H1 H2 H3 H4 H5 H6.

Scheme lc_set_Exp_ind' := Induction for lc_set_Exp Sort Prop.

Definition lc_set_Exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 =>
  lc_set_Exp_ind' H1 H2 H3 H4 H5 H6.

Scheme lc_set_Exp_rec' := Induction for lc_set_Exp Sort Set.

Definition lc_set_Exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 =>
  lc_set_Exp_rec' H1 H2 H3 H4 H5 H6.

Hint Constructors lc_Exp : core lngen.

Hint Constructors lc_set_Exp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_Typ_wrt_Typ t1 := forall typ1, lc_Typ (open_Typ_wrt_Typ t1 (t_var_f typ1)).

Hint Unfold body_Typ_wrt_Typ.

Definition body_Exp_wrt_Exp e1 := forall x1, lc_Exp (open_Exp_wrt_Exp e1 (e_var_f x1)).

Definition body_Exp_wrt_Typ e1 := forall typ1, lc_Exp (open_Exp_wrt_Typ e1 (t_var_f typ1)).

Hint Unfold body_Exp_wrt_Exp.

Hint Unfold body_Exp_wrt_Typ.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_Typ_min_mutual :
(forall t1, 1 <= size_Typ t1).
Proof. Admitted.

(* end hide *)

Lemma size_Typ_min :
forall t1, 1 <= size_Typ t1.
Proof. Admitted.

Hint Resolve size_Typ_min : lngen.

(* begin hide *)

Lemma size_Exp_min_mutual :
(forall e1, 1 <= size_Exp e1).
Proof. Admitted.

(* end hide *)

Lemma size_Exp_min :
forall e1, 1 <= size_Exp e1.
Proof. Admitted.

Hint Resolve size_Exp_min : lngen.

(* begin hide *)

Lemma size_Typ_close_Typ_wrt_Typ_rec_mutual :
(forall t1 typ1 n1,
  size_Typ (close_Typ_wrt_Typ_rec n1 typ1 t1) = size_Typ t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_Typ_close_Typ_wrt_Typ_rec :
forall t1 typ1 n1,
  size_Typ (close_Typ_wrt_Typ_rec n1 typ1 t1) = size_Typ t1.
Proof. Admitted.

Hint Resolve size_Typ_close_Typ_wrt_Typ_rec : lngen.
Hint Rewrite size_Typ_close_Typ_wrt_Typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Exp_close_Exp_wrt_Exp_rec_mutual :
(forall e1 x1 n1,
  size_Exp (close_Exp_wrt_Exp_rec n1 x1 e1) = size_Exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_Exp_close_Exp_wrt_Exp_rec :
forall e1 x1 n1,
  size_Exp (close_Exp_wrt_Exp_rec n1 x1 e1) = size_Exp e1.
Proof. Admitted.

Hint Resolve size_Exp_close_Exp_wrt_Exp_rec : lngen.
Hint Rewrite size_Exp_close_Exp_wrt_Exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Exp_close_Exp_wrt_Typ_rec_mutual :
(forall e1 typ1 n1,
  size_Exp (close_Exp_wrt_Typ_rec n1 typ1 e1) = size_Exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_Exp_close_Exp_wrt_Typ_rec :
forall e1 typ1 n1,
  size_Exp (close_Exp_wrt_Typ_rec n1 typ1 e1) = size_Exp e1.
Proof. Admitted.

Hint Resolve size_Exp_close_Exp_wrt_Typ_rec : lngen.
Hint Rewrite size_Exp_close_Exp_wrt_Typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_Typ_close_Typ_wrt_Typ :
forall t1 typ1,
  size_Typ (close_Typ_wrt_Typ typ1 t1) = size_Typ t1.
Proof. Admitted.

Hint Resolve size_Typ_close_Typ_wrt_Typ : lngen.
Hint Rewrite size_Typ_close_Typ_wrt_Typ using solve [auto] : lngen.

Lemma size_Exp_close_Exp_wrt_Exp :
forall e1 x1,
  size_Exp (close_Exp_wrt_Exp x1 e1) = size_Exp e1.
Proof. Admitted.

Hint Resolve size_Exp_close_Exp_wrt_Exp : lngen.
Hint Rewrite size_Exp_close_Exp_wrt_Exp using solve [auto] : lngen.

Lemma size_Exp_close_Exp_wrt_Typ :
forall e1 typ1,
  size_Exp (close_Exp_wrt_Typ typ1 e1) = size_Exp e1.
Proof. Admitted.

Hint Resolve size_Exp_close_Exp_wrt_Typ : lngen.
Hint Rewrite size_Exp_close_Exp_wrt_Typ using solve [auto] : lngen.

(* begin hide *)

Lemma size_Typ_open_Typ_wrt_Typ_rec_mutual :
(forall t1 t2 n1,
  size_Typ t1 <= size_Typ (open_Typ_wrt_Typ_rec n1 t2 t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_Typ_open_Typ_wrt_Typ_rec :
forall t1 t2 n1,
  size_Typ t1 <= size_Typ (open_Typ_wrt_Typ_rec n1 t2 t1).
Proof. Admitted.

Hint Resolve size_Typ_open_Typ_wrt_Typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Exp_open_Exp_wrt_Exp_rec_mutual :
(forall e1 e2 n1,
  size_Exp e1 <= size_Exp (open_Exp_wrt_Exp_rec n1 e2 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_Exp_open_Exp_wrt_Exp_rec :
forall e1 e2 n1,
  size_Exp e1 <= size_Exp (open_Exp_wrt_Exp_rec n1 e2 e1).
Proof. Admitted.

Hint Resolve size_Exp_open_Exp_wrt_Exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Exp_open_Exp_wrt_Typ_rec_mutual :
(forall e1 t1 n1,
  size_Exp e1 <= size_Exp (open_Exp_wrt_Typ_rec n1 t1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_Exp_open_Exp_wrt_Typ_rec :
forall e1 t1 n1,
  size_Exp e1 <= size_Exp (open_Exp_wrt_Typ_rec n1 t1 e1).
Proof. Admitted.

Hint Resolve size_Exp_open_Exp_wrt_Typ_rec : lngen.

(* end hide *)

Lemma size_Typ_open_Typ_wrt_Typ :
forall t1 t2,
  size_Typ t1 <= size_Typ (open_Typ_wrt_Typ t1 t2).
Proof. Admitted.

Hint Resolve size_Typ_open_Typ_wrt_Typ : lngen.

Lemma size_Exp_open_Exp_wrt_Exp :
forall e1 e2,
  size_Exp e1 <= size_Exp (open_Exp_wrt_Exp e1 e2).
Proof. Admitted.

Hint Resolve size_Exp_open_Exp_wrt_Exp : lngen.

Lemma size_Exp_open_Exp_wrt_Typ :
forall e1 t1,
  size_Exp e1 <= size_Exp (open_Exp_wrt_Typ e1 t1).
Proof. Admitted.

Hint Resolve size_Exp_open_Exp_wrt_Typ : lngen.

(* begin hide *)

Lemma size_Typ_open_Typ_wrt_Typ_rec_var_mutual :
(forall t1 typ1 n1,
  size_Typ (open_Typ_wrt_Typ_rec n1 (t_var_f typ1) t1) = size_Typ t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_Typ_open_Typ_wrt_Typ_rec_var :
forall t1 typ1 n1,
  size_Typ (open_Typ_wrt_Typ_rec n1 (t_var_f typ1) t1) = size_Typ t1.
Proof. Admitted.

Hint Resolve size_Typ_open_Typ_wrt_Typ_rec_var : lngen.
Hint Rewrite size_Typ_open_Typ_wrt_Typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Exp_open_Exp_wrt_Exp_rec_var_mutual :
(forall e1 x1 n1,
  size_Exp (open_Exp_wrt_Exp_rec n1 (e_var_f x1) e1) = size_Exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_Exp_open_Exp_wrt_Exp_rec_var :
forall e1 x1 n1,
  size_Exp (open_Exp_wrt_Exp_rec n1 (e_var_f x1) e1) = size_Exp e1.
Proof. Admitted.

Hint Resolve size_Exp_open_Exp_wrt_Exp_rec_var : lngen.
Hint Rewrite size_Exp_open_Exp_wrt_Exp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Exp_open_Exp_wrt_Typ_rec_var_mutual :
(forall e1 typ1 n1,
  size_Exp (open_Exp_wrt_Typ_rec n1 (t_var_f typ1) e1) = size_Exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_Exp_open_Exp_wrt_Typ_rec_var :
forall e1 typ1 n1,
  size_Exp (open_Exp_wrt_Typ_rec n1 (t_var_f typ1) e1) = size_Exp e1.
Proof. Admitted.

Hint Resolve size_Exp_open_Exp_wrt_Typ_rec_var : lngen.
Hint Rewrite size_Exp_open_Exp_wrt_Typ_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_Typ_open_Typ_wrt_Typ_var :
forall t1 typ1,
  size_Typ (open_Typ_wrt_Typ t1 (t_var_f typ1)) = size_Typ t1.
Proof. Admitted.

Hint Resolve size_Typ_open_Typ_wrt_Typ_var : lngen.
Hint Rewrite size_Typ_open_Typ_wrt_Typ_var using solve [auto] : lngen.

Lemma size_Exp_open_Exp_wrt_Exp_var :
forall e1 x1,
  size_Exp (open_Exp_wrt_Exp e1 (e_var_f x1)) = size_Exp e1.
Proof. Admitted.

Hint Resolve size_Exp_open_Exp_wrt_Exp_var : lngen.
Hint Rewrite size_Exp_open_Exp_wrt_Exp_var using solve [auto] : lngen.

Lemma size_Exp_open_Exp_wrt_Typ_var :
forall e1 typ1,
  size_Exp (open_Exp_wrt_Typ e1 (t_var_f typ1)) = size_Exp e1.
Proof. Admitted.

Hint Resolve size_Exp_open_Exp_wrt_Typ_var : lngen.
Hint Rewrite size_Exp_open_Exp_wrt_Typ_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_Typ_wrt_Typ_S_mutual :
(forall n1 t1,
  degree_Typ_wrt_Typ n1 t1 ->
  degree_Typ_wrt_Typ (S n1) t1).
Proof. Admitted.

(* end hide *)

Lemma degree_Typ_wrt_Typ_S :
forall n1 t1,
  degree_Typ_wrt_Typ n1 t1 ->
  degree_Typ_wrt_Typ (S n1) t1.
Proof. Admitted.

Hint Resolve degree_Typ_wrt_Typ_S : lngen.

(* begin hide *)

Lemma degree_Exp_wrt_Exp_S_mutual :
(forall n1 e1,
  degree_Exp_wrt_Exp n1 e1 ->
  degree_Exp_wrt_Exp (S n1) e1).
Proof. Admitted.

(* end hide *)

Lemma degree_Exp_wrt_Exp_S :
forall n1 e1,
  degree_Exp_wrt_Exp n1 e1 ->
  degree_Exp_wrt_Exp (S n1) e1.
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Exp_S : lngen.

(* begin hide *)

Lemma degree_Exp_wrt_Typ_S_mutual :
(forall n1 e1,
  degree_Exp_wrt_Typ n1 e1 ->
  degree_Exp_wrt_Typ (S n1) e1).
Proof. Admitted.

(* end hide *)

Lemma degree_Exp_wrt_Typ_S :
forall n1 e1,
  degree_Exp_wrt_Typ n1 e1 ->
  degree_Exp_wrt_Typ (S n1) e1.
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Typ_S : lngen.

Lemma degree_Typ_wrt_Typ_O :
forall n1 t1,
  degree_Typ_wrt_Typ O t1 ->
  degree_Typ_wrt_Typ n1 t1.
Proof. Admitted.

Hint Resolve degree_Typ_wrt_Typ_O : lngen.

Lemma degree_Exp_wrt_Exp_O :
forall n1 e1,
  degree_Exp_wrt_Exp O e1 ->
  degree_Exp_wrt_Exp n1 e1.
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Exp_O : lngen.

Lemma degree_Exp_wrt_Typ_O :
forall n1 e1,
  degree_Exp_wrt_Typ O e1 ->
  degree_Exp_wrt_Typ n1 e1.
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Typ_O : lngen.

(* begin hide *)

Lemma degree_Typ_wrt_Typ_close_Typ_wrt_Typ_rec_mutual :
(forall t1 typ1 n1,
  degree_Typ_wrt_Typ n1 t1 ->
  degree_Typ_wrt_Typ (S n1) (close_Typ_wrt_Typ_rec n1 typ1 t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Typ_wrt_Typ_close_Typ_wrt_Typ_rec :
forall t1 typ1 n1,
  degree_Typ_wrt_Typ n1 t1 ->
  degree_Typ_wrt_Typ (S n1) (close_Typ_wrt_Typ_rec n1 typ1 t1).
Proof. Admitted.

Hint Resolve degree_Typ_wrt_Typ_close_Typ_wrt_Typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Exp_close_Exp_wrt_Exp_rec_mutual :
(forall e1 x1 n1,
  degree_Exp_wrt_Exp n1 e1 ->
  degree_Exp_wrt_Exp (S n1) (close_Exp_wrt_Exp_rec n1 x1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Exp_close_Exp_wrt_Exp_rec :
forall e1 x1 n1,
  degree_Exp_wrt_Exp n1 e1 ->
  degree_Exp_wrt_Exp (S n1) (close_Exp_wrt_Exp_rec n1 x1 e1).
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Exp_close_Exp_wrt_Exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Exp_close_Exp_wrt_Typ_rec_mutual :
(forall e1 typ1 n1 n2,
  degree_Exp_wrt_Exp n2 e1 ->
  degree_Exp_wrt_Exp n2 (close_Exp_wrt_Typ_rec n1 typ1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Exp_close_Exp_wrt_Typ_rec :
forall e1 typ1 n1 n2,
  degree_Exp_wrt_Exp n2 e1 ->
  degree_Exp_wrt_Exp n2 (close_Exp_wrt_Typ_rec n1 typ1 e1).
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Exp_close_Exp_wrt_Typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Typ_close_Exp_wrt_Exp_rec_mutual :
(forall e1 x1 n1 n2,
  degree_Exp_wrt_Typ n2 e1 ->
  degree_Exp_wrt_Typ n2 (close_Exp_wrt_Exp_rec n1 x1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Typ_close_Exp_wrt_Exp_rec :
forall e1 x1 n1 n2,
  degree_Exp_wrt_Typ n2 e1 ->
  degree_Exp_wrt_Typ n2 (close_Exp_wrt_Exp_rec n1 x1 e1).
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Typ_close_Exp_wrt_Exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Typ_close_Exp_wrt_Typ_rec_mutual :
(forall e1 typ1 n1,
  degree_Exp_wrt_Typ n1 e1 ->
  degree_Exp_wrt_Typ (S n1) (close_Exp_wrt_Typ_rec n1 typ1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Typ_close_Exp_wrt_Typ_rec :
forall e1 typ1 n1,
  degree_Exp_wrt_Typ n1 e1 ->
  degree_Exp_wrt_Typ (S n1) (close_Exp_wrt_Typ_rec n1 typ1 e1).
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Typ_close_Exp_wrt_Typ_rec : lngen.

(* end hide *)

Lemma degree_Typ_wrt_Typ_close_Typ_wrt_Typ :
forall t1 typ1,
  degree_Typ_wrt_Typ 0 t1 ->
  degree_Typ_wrt_Typ 1 (close_Typ_wrt_Typ typ1 t1).
Proof. Admitted.

Hint Resolve degree_Typ_wrt_Typ_close_Typ_wrt_Typ : lngen.

Lemma degree_Exp_wrt_Exp_close_Exp_wrt_Exp :
forall e1 x1,
  degree_Exp_wrt_Exp 0 e1 ->
  degree_Exp_wrt_Exp 1 (close_Exp_wrt_Exp x1 e1).
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Exp_close_Exp_wrt_Exp : lngen.

Lemma degree_Exp_wrt_Exp_close_Exp_wrt_Typ :
forall e1 typ1 n1,
  degree_Exp_wrt_Exp n1 e1 ->
  degree_Exp_wrt_Exp n1 (close_Exp_wrt_Typ typ1 e1).
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Exp_close_Exp_wrt_Typ : lngen.

Lemma degree_Exp_wrt_Typ_close_Exp_wrt_Exp :
forall e1 x1 n1,
  degree_Exp_wrt_Typ n1 e1 ->
  degree_Exp_wrt_Typ n1 (close_Exp_wrt_Exp x1 e1).
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Typ_close_Exp_wrt_Exp : lngen.

Lemma degree_Exp_wrt_Typ_close_Exp_wrt_Typ :
forall e1 typ1,
  degree_Exp_wrt_Typ 0 e1 ->
  degree_Exp_wrt_Typ 1 (close_Exp_wrt_Typ typ1 e1).
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Typ_close_Exp_wrt_Typ : lngen.

(* begin hide *)

Lemma degree_Typ_wrt_Typ_close_Typ_wrt_Typ_rec_inv_mutual :
(forall t1 typ1 n1,
  degree_Typ_wrt_Typ (S n1) (close_Typ_wrt_Typ_rec n1 typ1 t1) ->
  degree_Typ_wrt_Typ n1 t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Typ_wrt_Typ_close_Typ_wrt_Typ_rec_inv :
forall t1 typ1 n1,
  degree_Typ_wrt_Typ (S n1) (close_Typ_wrt_Typ_rec n1 typ1 t1) ->
  degree_Typ_wrt_Typ n1 t1.
Proof. Admitted.

Hint Immediate degree_Typ_wrt_Typ_close_Typ_wrt_Typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Exp_close_Exp_wrt_Exp_rec_inv_mutual :
(forall e1 x1 n1,
  degree_Exp_wrt_Exp (S n1) (close_Exp_wrt_Exp_rec n1 x1 e1) ->
  degree_Exp_wrt_Exp n1 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Exp_close_Exp_wrt_Exp_rec_inv :
forall e1 x1 n1,
  degree_Exp_wrt_Exp (S n1) (close_Exp_wrt_Exp_rec n1 x1 e1) ->
  degree_Exp_wrt_Exp n1 e1.
Proof. Admitted.

Hint Immediate degree_Exp_wrt_Exp_close_Exp_wrt_Exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Exp_close_Exp_wrt_Typ_rec_inv_mutual :
(forall e1 typ1 n1 n2,
  degree_Exp_wrt_Exp n2 (close_Exp_wrt_Typ_rec n1 typ1 e1) ->
  degree_Exp_wrt_Exp n2 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Exp_close_Exp_wrt_Typ_rec_inv :
forall e1 typ1 n1 n2,
  degree_Exp_wrt_Exp n2 (close_Exp_wrt_Typ_rec n1 typ1 e1) ->
  degree_Exp_wrt_Exp n2 e1.
Proof. Admitted.

Hint Immediate degree_Exp_wrt_Exp_close_Exp_wrt_Typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Typ_close_Exp_wrt_Exp_rec_inv_mutual :
(forall e1 x1 n1 n2,
  degree_Exp_wrt_Typ n2 (close_Exp_wrt_Exp_rec n1 x1 e1) ->
  degree_Exp_wrt_Typ n2 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Typ_close_Exp_wrt_Exp_rec_inv :
forall e1 x1 n1 n2,
  degree_Exp_wrt_Typ n2 (close_Exp_wrt_Exp_rec n1 x1 e1) ->
  degree_Exp_wrt_Typ n2 e1.
Proof. Admitted.

Hint Immediate degree_Exp_wrt_Typ_close_Exp_wrt_Exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Typ_close_Exp_wrt_Typ_rec_inv_mutual :
(forall e1 typ1 n1,
  degree_Exp_wrt_Typ (S n1) (close_Exp_wrt_Typ_rec n1 typ1 e1) ->
  degree_Exp_wrt_Typ n1 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Typ_close_Exp_wrt_Typ_rec_inv :
forall e1 typ1 n1,
  degree_Exp_wrt_Typ (S n1) (close_Exp_wrt_Typ_rec n1 typ1 e1) ->
  degree_Exp_wrt_Typ n1 e1.
Proof. Admitted.

Hint Immediate degree_Exp_wrt_Typ_close_Exp_wrt_Typ_rec_inv : lngen.

(* end hide *)

Lemma degree_Typ_wrt_Typ_close_Typ_wrt_Typ_inv :
forall t1 typ1,
  degree_Typ_wrt_Typ 1 (close_Typ_wrt_Typ typ1 t1) ->
  degree_Typ_wrt_Typ 0 t1.
Proof. Admitted.

Hint Immediate degree_Typ_wrt_Typ_close_Typ_wrt_Typ_inv : lngen.

Lemma degree_Exp_wrt_Exp_close_Exp_wrt_Exp_inv :
forall e1 x1,
  degree_Exp_wrt_Exp 1 (close_Exp_wrt_Exp x1 e1) ->
  degree_Exp_wrt_Exp 0 e1.
Proof. Admitted.

Hint Immediate degree_Exp_wrt_Exp_close_Exp_wrt_Exp_inv : lngen.

Lemma degree_Exp_wrt_Exp_close_Exp_wrt_Typ_inv :
forall e1 typ1 n1,
  degree_Exp_wrt_Exp n1 (close_Exp_wrt_Typ typ1 e1) ->
  degree_Exp_wrt_Exp n1 e1.
Proof. Admitted.

Hint Immediate degree_Exp_wrt_Exp_close_Exp_wrt_Typ_inv : lngen.

Lemma degree_Exp_wrt_Typ_close_Exp_wrt_Exp_inv :
forall e1 x1 n1,
  degree_Exp_wrt_Typ n1 (close_Exp_wrt_Exp x1 e1) ->
  degree_Exp_wrt_Typ n1 e1.
Proof. Admitted.

Hint Immediate degree_Exp_wrt_Typ_close_Exp_wrt_Exp_inv : lngen.

Lemma degree_Exp_wrt_Typ_close_Exp_wrt_Typ_inv :
forall e1 typ1,
  degree_Exp_wrt_Typ 1 (close_Exp_wrt_Typ typ1 e1) ->
  degree_Exp_wrt_Typ 0 e1.
Proof. Admitted.

Hint Immediate degree_Exp_wrt_Typ_close_Exp_wrt_Typ_inv : lngen.

(* begin hide *)

Lemma degree_Typ_wrt_Typ_open_Typ_wrt_Typ_rec_mutual :
(forall t1 t2 n1,
  degree_Typ_wrt_Typ (S n1) t1 ->
  degree_Typ_wrt_Typ n1 t2 ->
  degree_Typ_wrt_Typ n1 (open_Typ_wrt_Typ_rec n1 t2 t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Typ_wrt_Typ_open_Typ_wrt_Typ_rec :
forall t1 t2 n1,
  degree_Typ_wrt_Typ (S n1) t1 ->
  degree_Typ_wrt_Typ n1 t2 ->
  degree_Typ_wrt_Typ n1 (open_Typ_wrt_Typ_rec n1 t2 t1).
Proof. Admitted.

Hint Resolve degree_Typ_wrt_Typ_open_Typ_wrt_Typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Exp_open_Exp_wrt_Exp_rec_mutual :
(forall e1 e2 n1,
  degree_Exp_wrt_Exp (S n1) e1 ->
  degree_Exp_wrt_Exp n1 e2 ->
  degree_Exp_wrt_Exp n1 (open_Exp_wrt_Exp_rec n1 e2 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Exp_open_Exp_wrt_Exp_rec :
forall e1 e2 n1,
  degree_Exp_wrt_Exp (S n1) e1 ->
  degree_Exp_wrt_Exp n1 e2 ->
  degree_Exp_wrt_Exp n1 (open_Exp_wrt_Exp_rec n1 e2 e1).
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Exp_open_Exp_wrt_Exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Exp_open_Exp_wrt_Typ_rec_mutual :
(forall e1 t1 n1 n2,
  degree_Exp_wrt_Exp n1 e1 ->
  degree_Exp_wrt_Exp n1 (open_Exp_wrt_Typ_rec n2 t1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Exp_open_Exp_wrt_Typ_rec :
forall e1 t1 n1 n2,
  degree_Exp_wrt_Exp n1 e1 ->
  degree_Exp_wrt_Exp n1 (open_Exp_wrt_Typ_rec n2 t1 e1).
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Exp_open_Exp_wrt_Typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Typ_open_Exp_wrt_Exp_rec_mutual :
(forall e1 e2 n1 n2,
  degree_Exp_wrt_Typ n1 e1 ->
  degree_Exp_wrt_Typ n1 e2 ->
  degree_Exp_wrt_Typ n1 (open_Exp_wrt_Exp_rec n2 e2 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Typ_open_Exp_wrt_Exp_rec :
forall e1 e2 n1 n2,
  degree_Exp_wrt_Typ n1 e1 ->
  degree_Exp_wrt_Typ n1 e2 ->
  degree_Exp_wrt_Typ n1 (open_Exp_wrt_Exp_rec n2 e2 e1).
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Typ_open_Exp_wrt_Exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Typ_open_Exp_wrt_Typ_rec_mutual :
(forall e1 t1 n1,
  degree_Exp_wrt_Typ (S n1) e1 ->
  degree_Typ_wrt_Typ n1 t1 ->
  degree_Exp_wrt_Typ n1 (open_Exp_wrt_Typ_rec n1 t1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Typ_open_Exp_wrt_Typ_rec :
forall e1 t1 n1,
  degree_Exp_wrt_Typ (S n1) e1 ->
  degree_Typ_wrt_Typ n1 t1 ->
  degree_Exp_wrt_Typ n1 (open_Exp_wrt_Typ_rec n1 t1 e1).
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Typ_open_Exp_wrt_Typ_rec : lngen.

(* end hide *)

Lemma degree_Typ_wrt_Typ_open_Typ_wrt_Typ :
forall t1 t2,
  degree_Typ_wrt_Typ 1 t1 ->
  degree_Typ_wrt_Typ 0 t2 ->
  degree_Typ_wrt_Typ 0 (open_Typ_wrt_Typ t1 t2).
Proof. Admitted.

Hint Resolve degree_Typ_wrt_Typ_open_Typ_wrt_Typ : lngen.

Lemma degree_Exp_wrt_Exp_open_Exp_wrt_Exp :
forall e1 e2,
  degree_Exp_wrt_Exp 1 e1 ->
  degree_Exp_wrt_Exp 0 e2 ->
  degree_Exp_wrt_Exp 0 (open_Exp_wrt_Exp e1 e2).
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Exp_open_Exp_wrt_Exp : lngen.

Lemma degree_Exp_wrt_Exp_open_Exp_wrt_Typ :
forall e1 t1 n1,
  degree_Exp_wrt_Exp n1 e1 ->
  degree_Exp_wrt_Exp n1 (open_Exp_wrt_Typ e1 t1).
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Exp_open_Exp_wrt_Typ : lngen.

Lemma degree_Exp_wrt_Typ_open_Exp_wrt_Exp :
forall e1 e2 n1,
  degree_Exp_wrt_Typ n1 e1 ->
  degree_Exp_wrt_Typ n1 e2 ->
  degree_Exp_wrt_Typ n1 (open_Exp_wrt_Exp e1 e2).
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Typ_open_Exp_wrt_Exp : lngen.

Lemma degree_Exp_wrt_Typ_open_Exp_wrt_Typ :
forall e1 t1,
  degree_Exp_wrt_Typ 1 e1 ->
  degree_Typ_wrt_Typ 0 t1 ->
  degree_Exp_wrt_Typ 0 (open_Exp_wrt_Typ e1 t1).
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Typ_open_Exp_wrt_Typ : lngen.

(* begin hide *)

Lemma degree_Typ_wrt_Typ_open_Typ_wrt_Typ_rec_inv_mutual :
(forall t1 t2 n1,
  degree_Typ_wrt_Typ n1 (open_Typ_wrt_Typ_rec n1 t2 t1) ->
  degree_Typ_wrt_Typ (S n1) t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Typ_wrt_Typ_open_Typ_wrt_Typ_rec_inv :
forall t1 t2 n1,
  degree_Typ_wrt_Typ n1 (open_Typ_wrt_Typ_rec n1 t2 t1) ->
  degree_Typ_wrt_Typ (S n1) t1.
Proof. Admitted.

Hint Immediate degree_Typ_wrt_Typ_open_Typ_wrt_Typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Exp_open_Exp_wrt_Exp_rec_inv_mutual :
(forall e1 e2 n1,
  degree_Exp_wrt_Exp n1 (open_Exp_wrt_Exp_rec n1 e2 e1) ->
  degree_Exp_wrt_Exp (S n1) e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Exp_open_Exp_wrt_Exp_rec_inv :
forall e1 e2 n1,
  degree_Exp_wrt_Exp n1 (open_Exp_wrt_Exp_rec n1 e2 e1) ->
  degree_Exp_wrt_Exp (S n1) e1.
Proof. Admitted.

Hint Immediate degree_Exp_wrt_Exp_open_Exp_wrt_Exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Exp_open_Exp_wrt_Typ_rec_inv_mutual :
(forall e1 t1 n1 n2,
  degree_Exp_wrt_Exp n1 (open_Exp_wrt_Typ_rec n2 t1 e1) ->
  degree_Exp_wrt_Exp n1 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Exp_open_Exp_wrt_Typ_rec_inv :
forall e1 t1 n1 n2,
  degree_Exp_wrt_Exp n1 (open_Exp_wrt_Typ_rec n2 t1 e1) ->
  degree_Exp_wrt_Exp n1 e1.
Proof. Admitted.

Hint Immediate degree_Exp_wrt_Exp_open_Exp_wrt_Typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Typ_open_Exp_wrt_Exp_rec_inv_mutual :
(forall e1 e2 n1 n2,
  degree_Exp_wrt_Typ n1 (open_Exp_wrt_Exp_rec n2 e2 e1) ->
  degree_Exp_wrt_Typ n1 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Typ_open_Exp_wrt_Exp_rec_inv :
forall e1 e2 n1 n2,
  degree_Exp_wrt_Typ n1 (open_Exp_wrt_Exp_rec n2 e2 e1) ->
  degree_Exp_wrt_Typ n1 e1.
Proof. Admitted.

Hint Immediate degree_Exp_wrt_Typ_open_Exp_wrt_Exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Typ_open_Exp_wrt_Typ_rec_inv_mutual :
(forall e1 t1 n1,
  degree_Exp_wrt_Typ n1 (open_Exp_wrt_Typ_rec n1 t1 e1) ->
  degree_Exp_wrt_Typ (S n1) e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_Exp_wrt_Typ_open_Exp_wrt_Typ_rec_inv :
forall e1 t1 n1,
  degree_Exp_wrt_Typ n1 (open_Exp_wrt_Typ_rec n1 t1 e1) ->
  degree_Exp_wrt_Typ (S n1) e1.
Proof. Admitted.

Hint Immediate degree_Exp_wrt_Typ_open_Exp_wrt_Typ_rec_inv : lngen.

(* end hide *)

Lemma degree_Typ_wrt_Typ_open_Typ_wrt_Typ_inv :
forall t1 t2,
  degree_Typ_wrt_Typ 0 (open_Typ_wrt_Typ t1 t2) ->
  degree_Typ_wrt_Typ 1 t1.
Proof. Admitted.

Hint Immediate degree_Typ_wrt_Typ_open_Typ_wrt_Typ_inv : lngen.

Lemma degree_Exp_wrt_Exp_open_Exp_wrt_Exp_inv :
forall e1 e2,
  degree_Exp_wrt_Exp 0 (open_Exp_wrt_Exp e1 e2) ->
  degree_Exp_wrt_Exp 1 e1.
Proof. Admitted.

Hint Immediate degree_Exp_wrt_Exp_open_Exp_wrt_Exp_inv : lngen.

Lemma degree_Exp_wrt_Exp_open_Exp_wrt_Typ_inv :
forall e1 t1 n1,
  degree_Exp_wrt_Exp n1 (open_Exp_wrt_Typ e1 t1) ->
  degree_Exp_wrt_Exp n1 e1.
Proof. Admitted.

Hint Immediate degree_Exp_wrt_Exp_open_Exp_wrt_Typ_inv : lngen.

Lemma degree_Exp_wrt_Typ_open_Exp_wrt_Exp_inv :
forall e1 e2 n1,
  degree_Exp_wrt_Typ n1 (open_Exp_wrt_Exp e1 e2) ->
  degree_Exp_wrt_Typ n1 e1.
Proof. Admitted.

Hint Immediate degree_Exp_wrt_Typ_open_Exp_wrt_Exp_inv : lngen.

Lemma degree_Exp_wrt_Typ_open_Exp_wrt_Typ_inv :
forall e1 t1,
  degree_Exp_wrt_Typ 0 (open_Exp_wrt_Typ e1 t1) ->
  degree_Exp_wrt_Typ 1 e1.
Proof. Admitted.

Hint Immediate degree_Exp_wrt_Typ_open_Exp_wrt_Typ_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_Typ_wrt_Typ_rec_inj_mutual :
(forall t1 t2 typ1 n1,
  close_Typ_wrt_Typ_rec n1 typ1 t1 = close_Typ_wrt_Typ_rec n1 typ1 t2 ->
  t1 = t2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_Typ_wrt_Typ_rec_inj :
forall t1 t2 typ1 n1,
  close_Typ_wrt_Typ_rec n1 typ1 t1 = close_Typ_wrt_Typ_rec n1 typ1 t2 ->
  t1 = t2.
Proof. Admitted.

Hint Immediate close_Typ_wrt_Typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Exp_wrt_Exp_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_Exp_wrt_Exp_rec n1 x1 e1 = close_Exp_wrt_Exp_rec n1 x1 e2 ->
  e1 = e2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_Exp_wrt_Exp_rec_inj :
forall e1 e2 x1 n1,
  close_Exp_wrt_Exp_rec n1 x1 e1 = close_Exp_wrt_Exp_rec n1 x1 e2 ->
  e1 = e2.
Proof. Admitted.

Hint Immediate close_Exp_wrt_Exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Exp_wrt_Typ_rec_inj_mutual :
(forall e1 e2 typ1 n1,
  close_Exp_wrt_Typ_rec n1 typ1 e1 = close_Exp_wrt_Typ_rec n1 typ1 e2 ->
  e1 = e2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_Exp_wrt_Typ_rec_inj :
forall e1 e2 typ1 n1,
  close_Exp_wrt_Typ_rec n1 typ1 e1 = close_Exp_wrt_Typ_rec n1 typ1 e2 ->
  e1 = e2.
Proof. Admitted.

Hint Immediate close_Exp_wrt_Typ_rec_inj : lngen.

(* end hide *)

Lemma close_Typ_wrt_Typ_inj :
forall t1 t2 typ1,
  close_Typ_wrt_Typ typ1 t1 = close_Typ_wrt_Typ typ1 t2 ->
  t1 = t2.
Proof. Admitted.

Hint Immediate close_Typ_wrt_Typ_inj : lngen.

Lemma close_Exp_wrt_Exp_inj :
forall e1 e2 x1,
  close_Exp_wrt_Exp x1 e1 = close_Exp_wrt_Exp x1 e2 ->
  e1 = e2.
Proof. Admitted.

Hint Immediate close_Exp_wrt_Exp_inj : lngen.

Lemma close_Exp_wrt_Typ_inj :
forall e1 e2 typ1,
  close_Exp_wrt_Typ typ1 e1 = close_Exp_wrt_Typ typ1 e2 ->
  e1 = e2.
Proof. Admitted.

Hint Immediate close_Exp_wrt_Typ_inj : lngen.

(* begin hide *)

Lemma close_Typ_wrt_Typ_rec_open_Typ_wrt_Typ_rec_mutual :
(forall t1 typ1 n1,
  typ1 `notin` tt_fv_Typ t1 ->
  close_Typ_wrt_Typ_rec n1 typ1 (open_Typ_wrt_Typ_rec n1 (t_var_f typ1) t1) = t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_Typ_wrt_Typ_rec_open_Typ_wrt_Typ_rec :
forall t1 typ1 n1,
  typ1 `notin` tt_fv_Typ t1 ->
  close_Typ_wrt_Typ_rec n1 typ1 (open_Typ_wrt_Typ_rec n1 (t_var_f typ1) t1) = t1.
Proof. Admitted.

Hint Resolve close_Typ_wrt_Typ_rec_open_Typ_wrt_Typ_rec : lngen.
Hint Rewrite close_Typ_wrt_Typ_rec_open_Typ_wrt_Typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Exp_wrt_Exp_rec_open_Exp_wrt_Exp_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` e_fv_Exp e1 ->
  close_Exp_wrt_Exp_rec n1 x1 (open_Exp_wrt_Exp_rec n1 (e_var_f x1) e1) = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_Exp_wrt_Exp_rec_open_Exp_wrt_Exp_rec :
forall e1 x1 n1,
  x1 `notin` e_fv_Exp e1 ->
  close_Exp_wrt_Exp_rec n1 x1 (open_Exp_wrt_Exp_rec n1 (e_var_f x1) e1) = e1.
Proof. Admitted.

Hint Resolve close_Exp_wrt_Exp_rec_open_Exp_wrt_Exp_rec : lngen.
Hint Rewrite close_Exp_wrt_Exp_rec_open_Exp_wrt_Exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Exp_wrt_Typ_rec_open_Exp_wrt_Typ_rec_mutual :
(forall e1 typ1 n1,
  typ1 `notin` tt_fv_Exp e1 ->
  close_Exp_wrt_Typ_rec n1 typ1 (open_Exp_wrt_Typ_rec n1 (t_var_f typ1) e1) = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_Exp_wrt_Typ_rec_open_Exp_wrt_Typ_rec :
forall e1 typ1 n1,
  typ1 `notin` tt_fv_Exp e1 ->
  close_Exp_wrt_Typ_rec n1 typ1 (open_Exp_wrt_Typ_rec n1 (t_var_f typ1) e1) = e1.
Proof. Admitted.

Hint Resolve close_Exp_wrt_Typ_rec_open_Exp_wrt_Typ_rec : lngen.
Hint Rewrite close_Exp_wrt_Typ_rec_open_Exp_wrt_Typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_Typ_wrt_Typ_open_Typ_wrt_Typ :
forall t1 typ1,
  typ1 `notin` tt_fv_Typ t1 ->
  close_Typ_wrt_Typ typ1 (open_Typ_wrt_Typ t1 (t_var_f typ1)) = t1.
Proof. Admitted.

Hint Resolve close_Typ_wrt_Typ_open_Typ_wrt_Typ : lngen.
Hint Rewrite close_Typ_wrt_Typ_open_Typ_wrt_Typ using solve [auto] : lngen.

Lemma close_Exp_wrt_Exp_open_Exp_wrt_Exp :
forall e1 x1,
  x1 `notin` e_fv_Exp e1 ->
  close_Exp_wrt_Exp x1 (open_Exp_wrt_Exp e1 (e_var_f x1)) = e1.
Proof. Admitted.

Hint Resolve close_Exp_wrt_Exp_open_Exp_wrt_Exp : lngen.
Hint Rewrite close_Exp_wrt_Exp_open_Exp_wrt_Exp using solve [auto] : lngen.

Lemma close_Exp_wrt_Typ_open_Exp_wrt_Typ :
forall e1 typ1,
  typ1 `notin` tt_fv_Exp e1 ->
  close_Exp_wrt_Typ typ1 (open_Exp_wrt_Typ e1 (t_var_f typ1)) = e1.
Proof. Admitted.

Hint Resolve close_Exp_wrt_Typ_open_Exp_wrt_Typ : lngen.
Hint Rewrite close_Exp_wrt_Typ_open_Exp_wrt_Typ using solve [auto] : lngen.

(* begin hide *)

Lemma open_Typ_wrt_Typ_rec_close_Typ_wrt_Typ_rec_mutual :
(forall t1 typ1 n1,
  open_Typ_wrt_Typ_rec n1 (t_var_f typ1) (close_Typ_wrt_Typ_rec n1 typ1 t1) = t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_Typ_wrt_Typ_rec_close_Typ_wrt_Typ_rec :
forall t1 typ1 n1,
  open_Typ_wrt_Typ_rec n1 (t_var_f typ1) (close_Typ_wrt_Typ_rec n1 typ1 t1) = t1.
Proof. Admitted.

Hint Resolve open_Typ_wrt_Typ_rec_close_Typ_wrt_Typ_rec : lngen.
Hint Rewrite open_Typ_wrt_Typ_rec_close_Typ_wrt_Typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Exp_wrt_Exp_rec_close_Exp_wrt_Exp_rec_mutual :
(forall e1 x1 n1,
  open_Exp_wrt_Exp_rec n1 (e_var_f x1) (close_Exp_wrt_Exp_rec n1 x1 e1) = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_Exp_wrt_Exp_rec_close_Exp_wrt_Exp_rec :
forall e1 x1 n1,
  open_Exp_wrt_Exp_rec n1 (e_var_f x1) (close_Exp_wrt_Exp_rec n1 x1 e1) = e1.
Proof. Admitted.

Hint Resolve open_Exp_wrt_Exp_rec_close_Exp_wrt_Exp_rec : lngen.
Hint Rewrite open_Exp_wrt_Exp_rec_close_Exp_wrt_Exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Exp_wrt_Typ_rec_close_Exp_wrt_Typ_rec_mutual :
(forall e1 typ1 n1,
  open_Exp_wrt_Typ_rec n1 (t_var_f typ1) (close_Exp_wrt_Typ_rec n1 typ1 e1) = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_Exp_wrt_Typ_rec_close_Exp_wrt_Typ_rec :
forall e1 typ1 n1,
  open_Exp_wrt_Typ_rec n1 (t_var_f typ1) (close_Exp_wrt_Typ_rec n1 typ1 e1) = e1.
Proof. Admitted.

Hint Resolve open_Exp_wrt_Typ_rec_close_Exp_wrt_Typ_rec : lngen.
Hint Rewrite open_Exp_wrt_Typ_rec_close_Exp_wrt_Typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_Typ_wrt_Typ_close_Typ_wrt_Typ :
forall t1 typ1,
  open_Typ_wrt_Typ (close_Typ_wrt_Typ typ1 t1) (t_var_f typ1) = t1.
Proof. Admitted.

Hint Resolve open_Typ_wrt_Typ_close_Typ_wrt_Typ : lngen.
Hint Rewrite open_Typ_wrt_Typ_close_Typ_wrt_Typ using solve [auto] : lngen.

Lemma open_Exp_wrt_Exp_close_Exp_wrt_Exp :
forall e1 x1,
  open_Exp_wrt_Exp (close_Exp_wrt_Exp x1 e1) (e_var_f x1) = e1.
Proof. Admitted.

Hint Resolve open_Exp_wrt_Exp_close_Exp_wrt_Exp : lngen.
Hint Rewrite open_Exp_wrt_Exp_close_Exp_wrt_Exp using solve [auto] : lngen.

Lemma open_Exp_wrt_Typ_close_Exp_wrt_Typ :
forall e1 typ1,
  open_Exp_wrt_Typ (close_Exp_wrt_Typ typ1 e1) (t_var_f typ1) = e1.
Proof. Admitted.

Hint Resolve open_Exp_wrt_Typ_close_Exp_wrt_Typ : lngen.
Hint Rewrite open_Exp_wrt_Typ_close_Exp_wrt_Typ using solve [auto] : lngen.

(* begin hide *)

Lemma open_Typ_wrt_Typ_rec_inj_mutual :
(forall t2 t1 typ1 n1,
  typ1 `notin` tt_fv_Typ t2 ->
  typ1 `notin` tt_fv_Typ t1 ->
  open_Typ_wrt_Typ_rec n1 (t_var_f typ1) t2 = open_Typ_wrt_Typ_rec n1 (t_var_f typ1) t1 ->
  t2 = t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_Typ_wrt_Typ_rec_inj :
forall t2 t1 typ1 n1,
  typ1 `notin` tt_fv_Typ t2 ->
  typ1 `notin` tt_fv_Typ t1 ->
  open_Typ_wrt_Typ_rec n1 (t_var_f typ1) t2 = open_Typ_wrt_Typ_rec n1 (t_var_f typ1) t1 ->
  t2 = t1.
Proof. Admitted.

Hint Immediate open_Typ_wrt_Typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Exp_wrt_Exp_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` e_fv_Exp e2 ->
  x1 `notin` e_fv_Exp e1 ->
  open_Exp_wrt_Exp_rec n1 (e_var_f x1) e2 = open_Exp_wrt_Exp_rec n1 (e_var_f x1) e1 ->
  e2 = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_Exp_wrt_Exp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` e_fv_Exp e2 ->
  x1 `notin` e_fv_Exp e1 ->
  open_Exp_wrt_Exp_rec n1 (e_var_f x1) e2 = open_Exp_wrt_Exp_rec n1 (e_var_f x1) e1 ->
  e2 = e1.
Proof. Admitted.

Hint Immediate open_Exp_wrt_Exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Exp_wrt_Typ_rec_inj_mutual :
(forall e2 e1 typ1 n1,
  typ1 `notin` tt_fv_Exp e2 ->
  typ1 `notin` tt_fv_Exp e1 ->
  open_Exp_wrt_Typ_rec n1 (t_var_f typ1) e2 = open_Exp_wrt_Typ_rec n1 (t_var_f typ1) e1 ->
  e2 = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_Exp_wrt_Typ_rec_inj :
forall e2 e1 typ1 n1,
  typ1 `notin` tt_fv_Exp e2 ->
  typ1 `notin` tt_fv_Exp e1 ->
  open_Exp_wrt_Typ_rec n1 (t_var_f typ1) e2 = open_Exp_wrt_Typ_rec n1 (t_var_f typ1) e1 ->
  e2 = e1.
Proof. Admitted.

Hint Immediate open_Exp_wrt_Typ_rec_inj : lngen.

(* end hide *)

Lemma open_Typ_wrt_Typ_inj :
forall t2 t1 typ1,
  typ1 `notin` tt_fv_Typ t2 ->
  typ1 `notin` tt_fv_Typ t1 ->
  open_Typ_wrt_Typ t2 (t_var_f typ1) = open_Typ_wrt_Typ t1 (t_var_f typ1) ->
  t2 = t1.
Proof. Admitted.

Hint Immediate open_Typ_wrt_Typ_inj : lngen.

Lemma open_Exp_wrt_Exp_inj :
forall e2 e1 x1,
  x1 `notin` e_fv_Exp e2 ->
  x1 `notin` e_fv_Exp e1 ->
  open_Exp_wrt_Exp e2 (e_var_f x1) = open_Exp_wrt_Exp e1 (e_var_f x1) ->
  e2 = e1.
Proof. Admitted.

Hint Immediate open_Exp_wrt_Exp_inj : lngen.

Lemma open_Exp_wrt_Typ_inj :
forall e2 e1 typ1,
  typ1 `notin` tt_fv_Exp e2 ->
  typ1 `notin` tt_fv_Exp e1 ->
  open_Exp_wrt_Typ e2 (t_var_f typ1) = open_Exp_wrt_Typ e1 (t_var_f typ1) ->
  e2 = e1.
Proof. Admitted.

Hint Immediate open_Exp_wrt_Typ_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_Typ_wrt_Typ_of_lc_Typ_mutual :
(forall t1,
  lc_Typ t1 ->
  degree_Typ_wrt_Typ 0 t1).
Proof. Admitted.

(* end hide *)

Lemma degree_Typ_wrt_Typ_of_lc_Typ :
forall t1,
  lc_Typ t1 ->
  degree_Typ_wrt_Typ 0 t1.
Proof. Admitted.

Hint Resolve degree_Typ_wrt_Typ_of_lc_Typ : lngen.

(* begin hide *)

Lemma degree_Exp_wrt_Exp_of_lc_Exp_mutual :
(forall e1,
  lc_Exp e1 ->
  degree_Exp_wrt_Exp 0 e1).
Proof. Admitted.

(* end hide *)

Lemma degree_Exp_wrt_Exp_of_lc_Exp :
forall e1,
  lc_Exp e1 ->
  degree_Exp_wrt_Exp 0 e1.
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Exp_of_lc_Exp : lngen.

(* begin hide *)

Lemma degree_Exp_wrt_Typ_of_lc_Exp_mutual :
(forall e1,
  lc_Exp e1 ->
  degree_Exp_wrt_Typ 0 e1).
Proof. Admitted.

(* end hide *)

Lemma degree_Exp_wrt_Typ_of_lc_Exp :
forall e1,
  lc_Exp e1 ->
  degree_Exp_wrt_Typ 0 e1.
Proof. Admitted.

Hint Resolve degree_Exp_wrt_Typ_of_lc_Exp : lngen.

(* begin hide *)

Lemma lc_Typ_of_degree_size_mutual :
forall i1,
(forall t1,
  size_Typ t1 = i1 ->
  degree_Typ_wrt_Typ 0 t1 ->
  lc_Typ t1).
Proof. Admitted.

(* end hide *)

Lemma lc_Typ_of_degree :
forall t1,
  degree_Typ_wrt_Typ 0 t1 ->
  lc_Typ t1.
Proof. Admitted.

Hint Resolve lc_Typ_of_degree : lngen.

(* begin hide *)

Lemma lc_Exp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_Exp e1 = i1 ->
  degree_Exp_wrt_Exp 0 e1 ->
  degree_Exp_wrt_Typ 0 e1 ->
  lc_Exp e1).
Proof. Admitted.

(* end hide *)

Lemma lc_Exp_of_degree :
forall e1,
  degree_Exp_wrt_Exp 0 e1 ->
  degree_Exp_wrt_Typ 0 e1 ->
  lc_Exp e1.
Proof. Admitted.

Hint Resolve lc_Exp_of_degree : lngen.

Ltac Typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_Typ_wrt_Typ_of_lc_Typ in J1; clear H
          end).

Ltac Exp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_Exp_wrt_Exp_of_lc_Exp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_Exp_wrt_Typ_of_lc_Exp in J2; clear H
          end).

Lemma lc_t_all_exists :
forall typ1 t1,
  lc_Typ (open_Typ_wrt_Typ t1 (t_var_f typ1)) ->
  lc_Typ (t_all t1).
Proof. Admitted.

Lemma lc_e_lam_exists :
forall x1 t1 e1,
  lc_Typ t1 ->
  lc_Exp (open_Exp_wrt_Exp e1 (e_var_f x1)) ->
  lc_Exp (e_lam t1 e1).
Proof. Admitted.

Lemma lc_e_Lam_exists :
forall typ1 e1,
  lc_Exp (open_Exp_wrt_Typ e1 (t_var_f typ1)) ->
  lc_Exp (e_Lam e1).
Proof. Admitted.

Hint Extern 1 (lc_Typ (t_all _)) =>
  let typ1 := fresh in
  pick_fresh typ1;
  apply (lc_t_all_exists typ1).

Hint Extern 1 (lc_Exp (e_lam _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e_lam_exists x1).

Hint Extern 1 (lc_Exp (e_Lam _)) =>
  let typ1 := fresh in
  pick_fresh typ1;
  apply (lc_e_Lam_exists typ1).

Lemma lc_body_Typ_wrt_Typ :
forall t1 t2,
  body_Typ_wrt_Typ t1 ->
  lc_Typ t2 ->
  lc_Typ (open_Typ_wrt_Typ t1 t2).
Proof. Admitted.

Hint Resolve lc_body_Typ_wrt_Typ : lngen.

Lemma lc_body_Exp_wrt_Exp :
forall e1 e2,
  body_Exp_wrt_Exp e1 ->
  lc_Exp e2 ->
  lc_Exp (open_Exp_wrt_Exp e1 e2).
Proof. Admitted.

Hint Resolve lc_body_Exp_wrt_Exp : lngen.

Lemma lc_body_Exp_wrt_Typ :
forall e1 t1,
  body_Exp_wrt_Typ e1 ->
  lc_Typ t1 ->
  lc_Exp (open_Exp_wrt_Typ e1 t1).
Proof. Admitted.

Hint Resolve lc_body_Exp_wrt_Typ : lngen.

Lemma lc_body_t_all_1 :
forall t1,
  lc_Typ (t_all t1) ->
  body_Typ_wrt_Typ t1.
Proof. Admitted.

Hint Resolve lc_body_t_all_1 : lngen.

Lemma lc_body_e_lam_2 :
forall t1 e1,
  lc_Exp (e_lam t1 e1) ->
  body_Exp_wrt_Exp e1.
Proof. Admitted.

Hint Resolve lc_body_e_lam_2 : lngen.

Lemma lc_body_e_Lam_1 :
forall e1,
  lc_Exp (e_Lam e1) ->
  body_Exp_wrt_Typ e1.
Proof. Admitted.

Hint Resolve lc_body_e_Lam_1 : lngen.

(* begin hide *)

Lemma lc_Typ_unique_mutual :
(forall t1 (proof2 proof3 : lc_Typ t1), proof2 = proof3).
Proof. Admitted.

(* end hide *)

Lemma lc_Typ_unique :
forall t1 (proof2 proof3 : lc_Typ t1), proof2 = proof3.
Proof. Admitted.

Hint Resolve lc_Typ_unique : lngen.

(* begin hide *)

Lemma lc_Exp_unique_mutual :
(forall e1 (proof2 proof3 : lc_Exp e1), proof2 = proof3).
Proof. Admitted.

(* end hide *)

Lemma lc_Exp_unique :
forall e1 (proof2 proof3 : lc_Exp e1), proof2 = proof3.
Proof. Admitted.

Hint Resolve lc_Exp_unique : lngen.

(* begin hide *)

Lemma lc_Typ_of_lc_set_Typ_mutual :
(forall t1, lc_set_Typ t1 -> lc_Typ t1).
Proof. Admitted.

(* end hide *)

Lemma lc_Typ_of_lc_set_Typ :
forall t1, lc_set_Typ t1 -> lc_Typ t1.
Proof. Admitted.

Hint Resolve lc_Typ_of_lc_set_Typ : lngen.

(* begin hide *)

Lemma lc_Exp_of_lc_set_Exp_mutual :
(forall e1, lc_set_Exp e1 -> lc_Exp e1).
Proof. Admitted.

(* end hide *)

Lemma lc_Exp_of_lc_set_Exp :
forall e1, lc_set_Exp e1 -> lc_Exp e1.
Proof. Admitted.

Hint Resolve lc_Exp_of_lc_set_Exp : lngen.

(* begin hide *)

Lemma lc_set_Typ_of_lc_Typ_size_mutual :
forall i1,
(forall t1,
  size_Typ t1 = i1 ->
  lc_Typ t1 ->
  lc_set_Typ t1).
Proof. Admitted.

(* end hide *)

Lemma lc_set_Typ_of_lc_Typ :
forall t1,
  lc_Typ t1 ->
  lc_set_Typ t1.
Proof. Admitted.

Hint Resolve lc_set_Typ_of_lc_Typ : lngen.

(* begin hide *)

Lemma lc_set_Exp_of_lc_Exp_size_mutual :
forall i1,
(forall e1,
  size_Exp e1 = i1 ->
  lc_Exp e1 ->
  lc_set_Exp e1).
Proof. Admitted.

(* end hide *)

Lemma lc_set_Exp_of_lc_Exp :
forall e1,
  lc_Exp e1 ->
  lc_set_Exp e1.
Proof. Admitted.

Hint Resolve lc_set_Exp_of_lc_Exp : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_Typ_wrt_Typ_rec_degree_Typ_wrt_Typ_mutual :
(forall t1 typ1 n1,
  degree_Typ_wrt_Typ n1 t1 ->
  typ1 `notin` tt_fv_Typ t1 ->
  close_Typ_wrt_Typ_rec n1 typ1 t1 = t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_Typ_wrt_Typ_rec_degree_Typ_wrt_Typ :
forall t1 typ1 n1,
  degree_Typ_wrt_Typ n1 t1 ->
  typ1 `notin` tt_fv_Typ t1 ->
  close_Typ_wrt_Typ_rec n1 typ1 t1 = t1.
Proof. Admitted.

Hint Resolve close_Typ_wrt_Typ_rec_degree_Typ_wrt_Typ : lngen.
Hint Rewrite close_Typ_wrt_Typ_rec_degree_Typ_wrt_Typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Exp_wrt_Exp_rec_degree_Exp_wrt_Exp_mutual :
(forall e1 x1 n1,
  degree_Exp_wrt_Exp n1 e1 ->
  x1 `notin` e_fv_Exp e1 ->
  close_Exp_wrt_Exp_rec n1 x1 e1 = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_Exp_wrt_Exp_rec_degree_Exp_wrt_Exp :
forall e1 x1 n1,
  degree_Exp_wrt_Exp n1 e1 ->
  x1 `notin` e_fv_Exp e1 ->
  close_Exp_wrt_Exp_rec n1 x1 e1 = e1.
Proof. Admitted.

Hint Resolve close_Exp_wrt_Exp_rec_degree_Exp_wrt_Exp : lngen.
Hint Rewrite close_Exp_wrt_Exp_rec_degree_Exp_wrt_Exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Exp_wrt_Typ_rec_degree_Exp_wrt_Typ_mutual :
(forall e1 typ1 n1,
  degree_Exp_wrt_Typ n1 e1 ->
  typ1 `notin` tt_fv_Exp e1 ->
  close_Exp_wrt_Typ_rec n1 typ1 e1 = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_Exp_wrt_Typ_rec_degree_Exp_wrt_Typ :
forall e1 typ1 n1,
  degree_Exp_wrt_Typ n1 e1 ->
  typ1 `notin` tt_fv_Exp e1 ->
  close_Exp_wrt_Typ_rec n1 typ1 e1 = e1.
Proof. Admitted.

Hint Resolve close_Exp_wrt_Typ_rec_degree_Exp_wrt_Typ : lngen.
Hint Rewrite close_Exp_wrt_Typ_rec_degree_Exp_wrt_Typ using solve [auto] : lngen.

(* end hide *)

Lemma close_Typ_wrt_Typ_lc_Typ :
forall t1 typ1,
  lc_Typ t1 ->
  typ1 `notin` tt_fv_Typ t1 ->
  close_Typ_wrt_Typ typ1 t1 = t1.
Proof. Admitted.

Hint Resolve close_Typ_wrt_Typ_lc_Typ : lngen.
Hint Rewrite close_Typ_wrt_Typ_lc_Typ using solve [auto] : lngen.

Lemma close_Exp_wrt_Exp_lc_Exp :
forall e1 x1,
  lc_Exp e1 ->
  x1 `notin` e_fv_Exp e1 ->
  close_Exp_wrt_Exp x1 e1 = e1.
Proof. Admitted.

Hint Resolve close_Exp_wrt_Exp_lc_Exp : lngen.
Hint Rewrite close_Exp_wrt_Exp_lc_Exp using solve [auto] : lngen.

Lemma close_Exp_wrt_Typ_lc_Exp :
forall e1 typ1,
  lc_Exp e1 ->
  typ1 `notin` tt_fv_Exp e1 ->
  close_Exp_wrt_Typ typ1 e1 = e1.
Proof. Admitted.

Hint Resolve close_Exp_wrt_Typ_lc_Exp : lngen.
Hint Rewrite close_Exp_wrt_Typ_lc_Exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_Typ_wrt_Typ_rec_degree_Typ_wrt_Typ_mutual :
(forall t2 t1 n1,
  degree_Typ_wrt_Typ n1 t2 ->
  open_Typ_wrt_Typ_rec n1 t1 t2 = t2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_Typ_wrt_Typ_rec_degree_Typ_wrt_Typ :
forall t2 t1 n1,
  degree_Typ_wrt_Typ n1 t2 ->
  open_Typ_wrt_Typ_rec n1 t1 t2 = t2.
Proof. Admitted.

Hint Resolve open_Typ_wrt_Typ_rec_degree_Typ_wrt_Typ : lngen.
Hint Rewrite open_Typ_wrt_Typ_rec_degree_Typ_wrt_Typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Exp_wrt_Exp_rec_degree_Exp_wrt_Exp_mutual :
(forall e2 e1 n1,
  degree_Exp_wrt_Exp n1 e2 ->
  open_Exp_wrt_Exp_rec n1 e1 e2 = e2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_Exp_wrt_Exp_rec_degree_Exp_wrt_Exp :
forall e2 e1 n1,
  degree_Exp_wrt_Exp n1 e2 ->
  open_Exp_wrt_Exp_rec n1 e1 e2 = e2.
Proof. Admitted.

Hint Resolve open_Exp_wrt_Exp_rec_degree_Exp_wrt_Exp : lngen.
Hint Rewrite open_Exp_wrt_Exp_rec_degree_Exp_wrt_Exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Exp_wrt_Typ_rec_degree_Exp_wrt_Typ_mutual :
(forall e1 t1 n1,
  degree_Exp_wrt_Typ n1 e1 ->
  open_Exp_wrt_Typ_rec n1 t1 e1 = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_Exp_wrt_Typ_rec_degree_Exp_wrt_Typ :
forall e1 t1 n1,
  degree_Exp_wrt_Typ n1 e1 ->
  open_Exp_wrt_Typ_rec n1 t1 e1 = e1.
Proof. Admitted.

Hint Resolve open_Exp_wrt_Typ_rec_degree_Exp_wrt_Typ : lngen.
Hint Rewrite open_Exp_wrt_Typ_rec_degree_Exp_wrt_Typ using solve [auto] : lngen.

(* end hide *)

Lemma open_Typ_wrt_Typ_lc_Typ :
forall t2 t1,
  lc_Typ t2 ->
  open_Typ_wrt_Typ t2 t1 = t2.
Proof. Admitted.

Hint Resolve open_Typ_wrt_Typ_lc_Typ : lngen.
Hint Rewrite open_Typ_wrt_Typ_lc_Typ using solve [auto] : lngen.

Lemma open_Exp_wrt_Exp_lc_Exp :
forall e2 e1,
  lc_Exp e2 ->
  open_Exp_wrt_Exp e2 e1 = e2.
Proof. Admitted.

Hint Resolve open_Exp_wrt_Exp_lc_Exp : lngen.
Hint Rewrite open_Exp_wrt_Exp_lc_Exp using solve [auto] : lngen.

Lemma open_Exp_wrt_Typ_lc_Exp :
forall e1 t1,
  lc_Exp e1 ->
  open_Exp_wrt_Typ e1 t1 = e1.
Proof. Admitted.

Hint Resolve open_Exp_wrt_Typ_lc_Exp : lngen.
Hint Rewrite open_Exp_wrt_Typ_lc_Exp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma tt_fv_Typ_close_Typ_wrt_Typ_rec_mutual :
(forall t1 typ1 n1,
  tt_fv_Typ (close_Typ_wrt_Typ_rec n1 typ1 t1) [=] remove typ1 (tt_fv_Typ t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_Typ_close_Typ_wrt_Typ_rec :
forall t1 typ1 n1,
  tt_fv_Typ (close_Typ_wrt_Typ_rec n1 typ1 t1) [=] remove typ1 (tt_fv_Typ t1).
Proof. Admitted.

Hint Resolve tt_fv_Typ_close_Typ_wrt_Typ_rec : lngen.
Hint Rewrite tt_fv_Typ_close_Typ_wrt_Typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_Exp_close_Exp_wrt_Exp_rec_mutual :
(forall e1 x1 n1,
  e_fv_Exp (close_Exp_wrt_Exp_rec n1 x1 e1) [=] remove x1 (e_fv_Exp e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_fv_Exp_close_Exp_wrt_Exp_rec :
forall e1 x1 n1,
  e_fv_Exp (close_Exp_wrt_Exp_rec n1 x1 e1) [=] remove x1 (e_fv_Exp e1).
Proof. Admitted.

Hint Resolve e_fv_Exp_close_Exp_wrt_Exp_rec : lngen.
Hint Rewrite e_fv_Exp_close_Exp_wrt_Exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_Exp_close_Exp_wrt_Typ_rec_mutual :
(forall e1 typ1 n1,
  e_fv_Exp (close_Exp_wrt_Typ_rec n1 typ1 e1) [=] e_fv_Exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_fv_Exp_close_Exp_wrt_Typ_rec :
forall e1 typ1 n1,
  e_fv_Exp (close_Exp_wrt_Typ_rec n1 typ1 e1) [=] e_fv_Exp e1.
Proof. Admitted.

Hint Resolve e_fv_Exp_close_Exp_wrt_Typ_rec : lngen.
Hint Rewrite e_fv_Exp_close_Exp_wrt_Typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_Exp_close_Exp_wrt_Exp_rec_mutual :
(forall e1 x1 n1,
  tt_fv_Exp (close_Exp_wrt_Exp_rec n1 x1 e1) [=] tt_fv_Exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_Exp_close_Exp_wrt_Exp_rec :
forall e1 x1 n1,
  tt_fv_Exp (close_Exp_wrt_Exp_rec n1 x1 e1) [=] tt_fv_Exp e1.
Proof. Admitted.

Hint Resolve tt_fv_Exp_close_Exp_wrt_Exp_rec : lngen.
Hint Rewrite tt_fv_Exp_close_Exp_wrt_Exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_Exp_close_Exp_wrt_Typ_rec_mutual :
(forall e1 typ1 n1,
  tt_fv_Exp (close_Exp_wrt_Typ_rec n1 typ1 e1) [=] remove typ1 (tt_fv_Exp e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_Exp_close_Exp_wrt_Typ_rec :
forall e1 typ1 n1,
  tt_fv_Exp (close_Exp_wrt_Typ_rec n1 typ1 e1) [=] remove typ1 (tt_fv_Exp e1).
Proof. Admitted.

Hint Resolve tt_fv_Exp_close_Exp_wrt_Typ_rec : lngen.
Hint Rewrite tt_fv_Exp_close_Exp_wrt_Typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma tt_fv_Typ_close_Typ_wrt_Typ :
forall t1 typ1,
  tt_fv_Typ (close_Typ_wrt_Typ typ1 t1) [=] remove typ1 (tt_fv_Typ t1).
Proof. Admitted.

Hint Resolve tt_fv_Typ_close_Typ_wrt_Typ : lngen.
Hint Rewrite tt_fv_Typ_close_Typ_wrt_Typ using solve [auto] : lngen.

Lemma e_fv_Exp_close_Exp_wrt_Exp :
forall e1 x1,
  e_fv_Exp (close_Exp_wrt_Exp x1 e1) [=] remove x1 (e_fv_Exp e1).
Proof. Admitted.

Hint Resolve e_fv_Exp_close_Exp_wrt_Exp : lngen.
Hint Rewrite e_fv_Exp_close_Exp_wrt_Exp using solve [auto] : lngen.

Lemma e_fv_Exp_close_Exp_wrt_Typ :
forall e1 typ1,
  e_fv_Exp (close_Exp_wrt_Typ typ1 e1) [=] e_fv_Exp e1.
Proof. Admitted.

Hint Resolve e_fv_Exp_close_Exp_wrt_Typ : lngen.
Hint Rewrite e_fv_Exp_close_Exp_wrt_Typ using solve [auto] : lngen.

Lemma tt_fv_Exp_close_Exp_wrt_Exp :
forall e1 x1,
  tt_fv_Exp (close_Exp_wrt_Exp x1 e1) [=] tt_fv_Exp e1.
Proof. Admitted.

Hint Resolve tt_fv_Exp_close_Exp_wrt_Exp : lngen.
Hint Rewrite tt_fv_Exp_close_Exp_wrt_Exp using solve [auto] : lngen.

Lemma tt_fv_Exp_close_Exp_wrt_Typ :
forall e1 typ1,
  tt_fv_Exp (close_Exp_wrt_Typ typ1 e1) [=] remove typ1 (tt_fv_Exp e1).
Proof. Admitted.

Hint Resolve tt_fv_Exp_close_Exp_wrt_Typ : lngen.
Hint Rewrite tt_fv_Exp_close_Exp_wrt_Typ using solve [auto] : lngen.

(* begin hide *)

Lemma tt_fv_Typ_open_Typ_wrt_Typ_rec_lower_mutual :
(forall t1 t2 n1,
  tt_fv_Typ t1 [<=] tt_fv_Typ (open_Typ_wrt_Typ_rec n1 t2 t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_Typ_open_Typ_wrt_Typ_rec_lower :
forall t1 t2 n1,
  tt_fv_Typ t1 [<=] tt_fv_Typ (open_Typ_wrt_Typ_rec n1 t2 t1).
Proof. Admitted.

Hint Resolve tt_fv_Typ_open_Typ_wrt_Typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_Exp_open_Exp_wrt_Exp_rec_lower_mutual :
(forall e1 e2 n1,
  e_fv_Exp e1 [<=] e_fv_Exp (open_Exp_wrt_Exp_rec n1 e2 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_fv_Exp_open_Exp_wrt_Exp_rec_lower :
forall e1 e2 n1,
  e_fv_Exp e1 [<=] e_fv_Exp (open_Exp_wrt_Exp_rec n1 e2 e1).
Proof. Admitted.

Hint Resolve e_fv_Exp_open_Exp_wrt_Exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_Exp_open_Exp_wrt_Typ_rec_lower_mutual :
(forall e1 t1 n1,
  e_fv_Exp e1 [<=] e_fv_Exp (open_Exp_wrt_Typ_rec n1 t1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_fv_Exp_open_Exp_wrt_Typ_rec_lower :
forall e1 t1 n1,
  e_fv_Exp e1 [<=] e_fv_Exp (open_Exp_wrt_Typ_rec n1 t1 e1).
Proof. Admitted.

Hint Resolve e_fv_Exp_open_Exp_wrt_Typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_Exp_open_Exp_wrt_Exp_rec_lower_mutual :
(forall e1 e2 n1,
  tt_fv_Exp e1 [<=] tt_fv_Exp (open_Exp_wrt_Exp_rec n1 e2 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_Exp_open_Exp_wrt_Exp_rec_lower :
forall e1 e2 n1,
  tt_fv_Exp e1 [<=] tt_fv_Exp (open_Exp_wrt_Exp_rec n1 e2 e1).
Proof. Admitted.

Hint Resolve tt_fv_Exp_open_Exp_wrt_Exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_Exp_open_Exp_wrt_Typ_rec_lower_mutual :
(forall e1 t1 n1,
  tt_fv_Exp e1 [<=] tt_fv_Exp (open_Exp_wrt_Typ_rec n1 t1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_Exp_open_Exp_wrt_Typ_rec_lower :
forall e1 t1 n1,
  tt_fv_Exp e1 [<=] tt_fv_Exp (open_Exp_wrt_Typ_rec n1 t1 e1).
Proof. Admitted.

Hint Resolve tt_fv_Exp_open_Exp_wrt_Typ_rec_lower : lngen.

(* end hide *)

Lemma tt_fv_Typ_open_Typ_wrt_Typ_lower :
forall t1 t2,
  tt_fv_Typ t1 [<=] tt_fv_Typ (open_Typ_wrt_Typ t1 t2).
Proof. Admitted.

Hint Resolve tt_fv_Typ_open_Typ_wrt_Typ_lower : lngen.

Lemma e_fv_Exp_open_Exp_wrt_Exp_lower :
forall e1 e2,
  e_fv_Exp e1 [<=] e_fv_Exp (open_Exp_wrt_Exp e1 e2).
Proof. Admitted.

Hint Resolve e_fv_Exp_open_Exp_wrt_Exp_lower : lngen.

Lemma e_fv_Exp_open_Exp_wrt_Typ_lower :
forall e1 t1,
  e_fv_Exp e1 [<=] e_fv_Exp (open_Exp_wrt_Typ e1 t1).
Proof. Admitted.

Hint Resolve e_fv_Exp_open_Exp_wrt_Typ_lower : lngen.

Lemma tt_fv_Exp_open_Exp_wrt_Exp_lower :
forall e1 e2,
  tt_fv_Exp e1 [<=] tt_fv_Exp (open_Exp_wrt_Exp e1 e2).
Proof. Admitted.

Hint Resolve tt_fv_Exp_open_Exp_wrt_Exp_lower : lngen.

Lemma tt_fv_Exp_open_Exp_wrt_Typ_lower :
forall e1 t1,
  tt_fv_Exp e1 [<=] tt_fv_Exp (open_Exp_wrt_Typ e1 t1).
Proof. Admitted.

Hint Resolve tt_fv_Exp_open_Exp_wrt_Typ_lower : lngen.

(* begin hide *)

Lemma tt_fv_Typ_open_Typ_wrt_Typ_rec_upper_mutual :
(forall t1 t2 n1,
  tt_fv_Typ (open_Typ_wrt_Typ_rec n1 t2 t1) [<=] tt_fv_Typ t2 `union` tt_fv_Typ t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_Typ_open_Typ_wrt_Typ_rec_upper :
forall t1 t2 n1,
  tt_fv_Typ (open_Typ_wrt_Typ_rec n1 t2 t1) [<=] tt_fv_Typ t2 `union` tt_fv_Typ t1.
Proof. Admitted.

Hint Resolve tt_fv_Typ_open_Typ_wrt_Typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_Exp_open_Exp_wrt_Exp_rec_upper_mutual :
(forall e1 e2 n1,
  e_fv_Exp (open_Exp_wrt_Exp_rec n1 e2 e1) [<=] e_fv_Exp e2 `union` e_fv_Exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_fv_Exp_open_Exp_wrt_Exp_rec_upper :
forall e1 e2 n1,
  e_fv_Exp (open_Exp_wrt_Exp_rec n1 e2 e1) [<=] e_fv_Exp e2 `union` e_fv_Exp e1.
Proof. Admitted.

Hint Resolve e_fv_Exp_open_Exp_wrt_Exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_Exp_open_Exp_wrt_Typ_rec_upper_mutual :
(forall e1 t1 n1,
  e_fv_Exp (open_Exp_wrt_Typ_rec n1 t1 e1) [<=] e_fv_Exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_fv_Exp_open_Exp_wrt_Typ_rec_upper :
forall e1 t1 n1,
  e_fv_Exp (open_Exp_wrt_Typ_rec n1 t1 e1) [<=] e_fv_Exp e1.
Proof. Admitted.

Hint Resolve e_fv_Exp_open_Exp_wrt_Typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_Exp_open_Exp_wrt_Exp_rec_upper_mutual :
(forall e1 e2 n1,
  tt_fv_Exp (open_Exp_wrt_Exp_rec n1 e2 e1) [<=] tt_fv_Exp e2 `union` tt_fv_Exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_Exp_open_Exp_wrt_Exp_rec_upper :
forall e1 e2 n1,
  tt_fv_Exp (open_Exp_wrt_Exp_rec n1 e2 e1) [<=] tt_fv_Exp e2 `union` tt_fv_Exp e1.
Proof. Admitted.

Hint Resolve tt_fv_Exp_open_Exp_wrt_Exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_Exp_open_Exp_wrt_Typ_rec_upper_mutual :
(forall e1 t1 n1,
  tt_fv_Exp (open_Exp_wrt_Typ_rec n1 t1 e1) [<=] tt_fv_Typ t1 `union` tt_fv_Exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_Exp_open_Exp_wrt_Typ_rec_upper :
forall e1 t1 n1,
  tt_fv_Exp (open_Exp_wrt_Typ_rec n1 t1 e1) [<=] tt_fv_Typ t1 `union` tt_fv_Exp e1.
Proof. Admitted.

Hint Resolve tt_fv_Exp_open_Exp_wrt_Typ_rec_upper : lngen.

(* end hide *)

Lemma tt_fv_Typ_open_Typ_wrt_Typ_upper :
forall t1 t2,
  tt_fv_Typ (open_Typ_wrt_Typ t1 t2) [<=] tt_fv_Typ t2 `union` tt_fv_Typ t1.
Proof. Admitted.

Hint Resolve tt_fv_Typ_open_Typ_wrt_Typ_upper : lngen.

Lemma e_fv_Exp_open_Exp_wrt_Exp_upper :
forall e1 e2,
  e_fv_Exp (open_Exp_wrt_Exp e1 e2) [<=] e_fv_Exp e2 `union` e_fv_Exp e1.
Proof. Admitted.

Hint Resolve e_fv_Exp_open_Exp_wrt_Exp_upper : lngen.

Lemma e_fv_Exp_open_Exp_wrt_Typ_upper :
forall e1 t1,
  e_fv_Exp (open_Exp_wrt_Typ e1 t1) [<=] e_fv_Exp e1.
Proof. Admitted.

Hint Resolve e_fv_Exp_open_Exp_wrt_Typ_upper : lngen.

Lemma tt_fv_Exp_open_Exp_wrt_Exp_upper :
forall e1 e2,
  tt_fv_Exp (open_Exp_wrt_Exp e1 e2) [<=] tt_fv_Exp e2 `union` tt_fv_Exp e1.
Proof. Admitted.

Hint Resolve tt_fv_Exp_open_Exp_wrt_Exp_upper : lngen.

Lemma tt_fv_Exp_open_Exp_wrt_Typ_upper :
forall e1 t1,
  tt_fv_Exp (open_Exp_wrt_Typ e1 t1) [<=] tt_fv_Typ t1 `union` tt_fv_Exp e1.
Proof. Admitted.

Hint Resolve tt_fv_Exp_open_Exp_wrt_Typ_upper : lngen.

(* begin hide *)

Lemma tt_fv_Typ_t_subst_Typ_fresh_mutual :
(forall t1 t2 typ1,
  typ1 `notin` tt_fv_Typ t1 ->
  tt_fv_Typ (t_subst_Typ t2 typ1 t1) [=] tt_fv_Typ t1).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_Typ_t_subst_Typ_fresh :
forall t1 t2 typ1,
  typ1 `notin` tt_fv_Typ t1 ->
  tt_fv_Typ (t_subst_Typ t2 typ1 t1) [=] tt_fv_Typ t1.
Proof. Admitted.

Hint Resolve tt_fv_Typ_t_subst_Typ_fresh : lngen.
Hint Rewrite tt_fv_Typ_t_subst_Typ_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma e_fv_Exp_e_subst_Exp_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` e_fv_Exp e1 ->
  e_fv_Exp (e_subst_Exp e2 x1 e1) [=] e_fv_Exp e1).
Proof. Admitted.

(* end hide *)

Lemma e_fv_Exp_e_subst_Exp_fresh :
forall e1 e2 x1,
  x1 `notin` e_fv_Exp e1 ->
  e_fv_Exp (e_subst_Exp e2 x1 e1) [=] e_fv_Exp e1.
Proof. Admitted.

Hint Resolve e_fv_Exp_e_subst_Exp_fresh : lngen.
Hint Rewrite e_fv_Exp_e_subst_Exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tt_fv_Exp_e_subst_Exp_fresh_mutual :
(forall e1 t1 typ1,
  e_fv_Exp (t_subst_Exp t1 typ1 e1) [=] e_fv_Exp e1).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_Exp_e_subst_Exp_fresh :
forall e1 t1 typ1,
  e_fv_Exp (t_subst_Exp t1 typ1 e1) [=] e_fv_Exp e1.
Proof. Admitted.

Hint Resolve tt_fv_Exp_e_subst_Exp_fresh : lngen.
Hint Rewrite tt_fv_Exp_e_subst_Exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tt_fv_Exp_t_subst_Exp_fresh_mutual :
(forall e1 t1 typ1,
  typ1 `notin` tt_fv_Exp e1 ->
  tt_fv_Exp (t_subst_Exp t1 typ1 e1) [=] tt_fv_Exp e1).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_Exp_t_subst_Exp_fresh :
forall e1 t1 typ1,
  typ1 `notin` tt_fv_Exp e1 ->
  tt_fv_Exp (t_subst_Exp t1 typ1 e1) [=] tt_fv_Exp e1.
Proof. Admitted.

Hint Resolve tt_fv_Exp_t_subst_Exp_fresh : lngen.
Hint Rewrite tt_fv_Exp_t_subst_Exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tt_fv_Typ_t_subst_Typ_lower_mutual :
(forall t1 t2 typ1,
  remove typ1 (tt_fv_Typ t1) [<=] tt_fv_Typ (t_subst_Typ t2 typ1 t1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_Typ_t_subst_Typ_lower :
forall t1 t2 typ1,
  remove typ1 (tt_fv_Typ t1) [<=] tt_fv_Typ (t_subst_Typ t2 typ1 t1).
Proof. Admitted.

Hint Resolve tt_fv_Typ_t_subst_Typ_lower : lngen.

(* begin hide *)

Lemma e_fv_Exp_e_subst_Exp_lower_mutual :
(forall e1 e2 x1,
  remove x1 (e_fv_Exp e1) [<=] e_fv_Exp (e_subst_Exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma e_fv_Exp_e_subst_Exp_lower :
forall e1 e2 x1,
  remove x1 (e_fv_Exp e1) [<=] e_fv_Exp (e_subst_Exp e2 x1 e1).
Proof. Admitted.

Hint Resolve e_fv_Exp_e_subst_Exp_lower : lngen.

(* begin hide *)

Lemma e_fv_Exp_t_subst_Exp_lower_mutual :
(forall e1 t1 typ1,
  e_fv_Exp e1 [<=] e_fv_Exp (t_subst_Exp t1 typ1 e1)).
Proof. Admitted.

(* end hide *)

Lemma e_fv_Exp_t_subst_Exp_lower :
forall e1 t1 typ1,
  e_fv_Exp e1 [<=] e_fv_Exp (t_subst_Exp t1 typ1 e1).
Proof. Admitted.

Hint Resolve e_fv_Exp_t_subst_Exp_lower : lngen.

(* begin hide *)

Lemma tt_fv_Exp_e_subst_Exp_lower_mutual :
(forall e1 e2 x1,
  tt_fv_Exp e1 [<=] tt_fv_Exp (e_subst_Exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_Exp_e_subst_Exp_lower :
forall e1 e2 x1,
  tt_fv_Exp e1 [<=] tt_fv_Exp (e_subst_Exp e2 x1 e1).
Proof. Admitted.

Hint Resolve tt_fv_Exp_e_subst_Exp_lower : lngen.

(* begin hide *)

Lemma tt_fv_Exp_t_subst_Exp_lower_mutual :
(forall e1 t1 typ1,
  remove typ1 (tt_fv_Exp e1) [<=] tt_fv_Exp (t_subst_Exp t1 typ1 e1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_Exp_t_subst_Exp_lower :
forall e1 t1 typ1,
  remove typ1 (tt_fv_Exp e1) [<=] tt_fv_Exp (t_subst_Exp t1 typ1 e1).
Proof. Admitted.

Hint Resolve tt_fv_Exp_t_subst_Exp_lower : lngen.

(* begin hide *)

Lemma tt_fv_Typ_t_subst_Typ_notin_mutual :
(forall t1 t2 typ1 typ2,
  typ2 `notin` tt_fv_Typ t1 ->
  typ2 `notin` tt_fv_Typ t2 ->
  typ2 `notin` tt_fv_Typ (t_subst_Typ t2 typ1 t1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_Typ_t_subst_Typ_notin :
forall t1 t2 typ1 typ2,
  typ2 `notin` tt_fv_Typ t1 ->
  typ2 `notin` tt_fv_Typ t2 ->
  typ2 `notin` tt_fv_Typ (t_subst_Typ t2 typ1 t1).
Proof. Admitted.

Hint Resolve tt_fv_Typ_t_subst_Typ_notin : lngen.

(* begin hide *)

Lemma e_fv_Exp_e_subst_Exp_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` e_fv_Exp e1 ->
  x2 `notin` e_fv_Exp e2 ->
  x2 `notin` e_fv_Exp (e_subst_Exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma e_fv_Exp_e_subst_Exp_notin :
forall e1 e2 x1 x2,
  x2 `notin` e_fv_Exp e1 ->
  x2 `notin` e_fv_Exp e2 ->
  x2 `notin` e_fv_Exp (e_subst_Exp e2 x1 e1).
Proof. Admitted.

Hint Resolve e_fv_Exp_e_subst_Exp_notin : lngen.

(* begin hide *)

Lemma e_fv_Exp_t_subst_Exp_notin_mutual :
(forall e1 t1 typ1 x1,
  x1 `notin` e_fv_Exp e1 ->
  x1 `notin` e_fv_Exp (t_subst_Exp t1 typ1 e1)).
Proof. Admitted.

(* end hide *)

Lemma e_fv_Exp_t_subst_Exp_notin :
forall e1 t1 typ1 x1,
  x1 `notin` e_fv_Exp e1 ->
  x1 `notin` e_fv_Exp (t_subst_Exp t1 typ1 e1).
Proof. Admitted.

Hint Resolve e_fv_Exp_t_subst_Exp_notin : lngen.

(* begin hide *)

Lemma tt_fv_Exp_e_subst_Exp_notin_mutual :
(forall e1 e2 x1 typ1,
  typ1 `notin` tt_fv_Exp e1 ->
  typ1 `notin` tt_fv_Exp e2 ->
  typ1 `notin` tt_fv_Exp (e_subst_Exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_Exp_e_subst_Exp_notin :
forall e1 e2 x1 typ1,
  typ1 `notin` tt_fv_Exp e1 ->
  typ1 `notin` tt_fv_Exp e2 ->
  typ1 `notin` tt_fv_Exp (e_subst_Exp e2 x1 e1).
Proof. Admitted.

Hint Resolve tt_fv_Exp_e_subst_Exp_notin : lngen.

(* begin hide *)

Lemma tt_fv_Exp_t_subst_Exp_notin_mutual :
(forall e1 t1 typ1 typ2,
  typ2 `notin` tt_fv_Exp e1 ->
  typ2 `notin` tt_fv_Typ t1 ->
  typ2 `notin` tt_fv_Exp (t_subst_Exp t1 typ1 e1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_Exp_t_subst_Exp_notin :
forall e1 t1 typ1 typ2,
  typ2 `notin` tt_fv_Exp e1 ->
  typ2 `notin` tt_fv_Typ t1 ->
  typ2 `notin` tt_fv_Exp (t_subst_Exp t1 typ1 e1).
Proof. Admitted.

Hint Resolve tt_fv_Exp_t_subst_Exp_notin : lngen.

(* begin hide *)

Lemma tt_fv_Typ_t_subst_Typ_upper_mutual :
(forall t1 t2 typ1,
  tt_fv_Typ (t_subst_Typ t2 typ1 t1) [<=] tt_fv_Typ t2 `union` remove typ1 (tt_fv_Typ t1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_Typ_t_subst_Typ_upper :
forall t1 t2 typ1,
  tt_fv_Typ (t_subst_Typ t2 typ1 t1) [<=] tt_fv_Typ t2 `union` remove typ1 (tt_fv_Typ t1).
Proof. Admitted.

Hint Resolve tt_fv_Typ_t_subst_Typ_upper : lngen.

(* begin hide *)

Lemma e_fv_Exp_e_subst_Exp_upper_mutual :
(forall e1 e2 x1,
  e_fv_Exp (e_subst_Exp e2 x1 e1) [<=] e_fv_Exp e2 `union` remove x1 (e_fv_Exp e1)).
Proof. Admitted.

(* end hide *)

Lemma e_fv_Exp_e_subst_Exp_upper :
forall e1 e2 x1,
  e_fv_Exp (e_subst_Exp e2 x1 e1) [<=] e_fv_Exp e2 `union` remove x1 (e_fv_Exp e1).
Proof. Admitted.

Hint Resolve e_fv_Exp_e_subst_Exp_upper : lngen.

(* begin hide *)

Lemma e_fv_Exp_t_subst_Exp_upper_mutual :
(forall e1 t1 typ1,
  e_fv_Exp (t_subst_Exp t1 typ1 e1) [<=] e_fv_Exp e1).
Proof. Admitted.

(* end hide *)

Lemma e_fv_Exp_t_subst_Exp_upper :
forall e1 t1 typ1,
  e_fv_Exp (t_subst_Exp t1 typ1 e1) [<=] e_fv_Exp e1.
Proof. Admitted.

Hint Resolve e_fv_Exp_t_subst_Exp_upper : lngen.

(* begin hide *)

Lemma tt_fv_Exp_e_subst_Exp_upper_mutual :
(forall e1 e2 x1,
  tt_fv_Exp (e_subst_Exp e2 x1 e1) [<=] tt_fv_Exp e2 `union` tt_fv_Exp e1).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_Exp_e_subst_Exp_upper :
forall e1 e2 x1,
  tt_fv_Exp (e_subst_Exp e2 x1 e1) [<=] tt_fv_Exp e2 `union` tt_fv_Exp e1.
Proof. Admitted.

Hint Resolve tt_fv_Exp_e_subst_Exp_upper : lngen.

(* begin hide *)

Lemma tt_fv_Exp_t_subst_Exp_upper_mutual :
(forall e1 t1 typ1,
  tt_fv_Exp (t_subst_Exp t1 typ1 e1) [<=] tt_fv_Typ t1 `union` remove typ1 (tt_fv_Exp e1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_Exp_t_subst_Exp_upper :
forall e1 t1 typ1,
  tt_fv_Exp (t_subst_Exp t1 typ1 e1) [<=] tt_fv_Typ t1 `union` remove typ1 (tt_fv_Exp e1).
Proof. Admitted.

Hint Resolve tt_fv_Exp_t_subst_Exp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma t_subst_Typ_close_Typ_wrt_Typ_rec_mutual :
(forall t2 t1 typ1 typ2 n1,
  degree_Typ_wrt_Typ n1 t1 ->
  typ1 <> typ2 ->
  typ2 `notin` tt_fv_Typ t1 ->
  t_subst_Typ t1 typ1 (close_Typ_wrt_Typ_rec n1 typ2 t2) = close_Typ_wrt_Typ_rec n1 typ2 (t_subst_Typ t1 typ1 t2)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Typ_close_Typ_wrt_Typ_rec :
forall t2 t1 typ1 typ2 n1,
  degree_Typ_wrt_Typ n1 t1 ->
  typ1 <> typ2 ->
  typ2 `notin` tt_fv_Typ t1 ->
  t_subst_Typ t1 typ1 (close_Typ_wrt_Typ_rec n1 typ2 t2) = close_Typ_wrt_Typ_rec n1 typ2 (t_subst_Typ t1 typ1 t2).
Proof. Admitted.

Hint Resolve t_subst_Typ_close_Typ_wrt_Typ_rec : lngen.

(* begin hide *)

Lemma e_subst_Exp_close_Exp_wrt_Exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_Exp_wrt_Exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` e_fv_Exp e1 ->
  e_subst_Exp e1 x1 (close_Exp_wrt_Exp_rec n1 x2 e2) = close_Exp_wrt_Exp_rec n1 x2 (e_subst_Exp e1 x1 e2)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_Exp_close_Exp_wrt_Exp_rec :
forall e2 e1 x1 x2 n1,
  degree_Exp_wrt_Exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` e_fv_Exp e1 ->
  e_subst_Exp e1 x1 (close_Exp_wrt_Exp_rec n1 x2 e2) = close_Exp_wrt_Exp_rec n1 x2 (e_subst_Exp e1 x1 e2).
Proof. Admitted.

Hint Resolve e_subst_Exp_close_Exp_wrt_Exp_rec : lngen.

(* begin hide *)

Lemma e_subst_Exp_close_Exp_wrt_Typ_rec_mutual :
(forall e2 e1 typ1 x1 n1,
  degree_Exp_wrt_Typ n1 e1 ->
  x1 `notin` tt_fv_Exp e1 ->
  e_subst_Exp e1 typ1 (close_Exp_wrt_Typ_rec n1 x1 e2) = close_Exp_wrt_Typ_rec n1 x1 (e_subst_Exp e1 typ1 e2)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_Exp_close_Exp_wrt_Typ_rec :
forall e2 e1 typ1 x1 n1,
  degree_Exp_wrt_Typ n1 e1 ->
  x1 `notin` tt_fv_Exp e1 ->
  e_subst_Exp e1 typ1 (close_Exp_wrt_Typ_rec n1 x1 e2) = close_Exp_wrt_Typ_rec n1 x1 (e_subst_Exp e1 typ1 e2).
Proof. Admitted.

Hint Resolve e_subst_Exp_close_Exp_wrt_Typ_rec : lngen.

(* begin hide *)

Lemma t_subst_Exp_close_Exp_wrt_Exp_rec_mutual :
(forall e1 t1 x1 typ1 n1,
  t_subst_Exp t1 x1 (close_Exp_wrt_Exp_rec n1 typ1 e1) = close_Exp_wrt_Exp_rec n1 typ1 (t_subst_Exp t1 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Exp_close_Exp_wrt_Exp_rec :
forall e1 t1 x1 typ1 n1,
  t_subst_Exp t1 x1 (close_Exp_wrt_Exp_rec n1 typ1 e1) = close_Exp_wrt_Exp_rec n1 typ1 (t_subst_Exp t1 x1 e1).
Proof. Admitted.

Hint Resolve t_subst_Exp_close_Exp_wrt_Exp_rec : lngen.

(* begin hide *)

Lemma t_subst_Exp_close_Exp_wrt_Typ_rec_mutual :
(forall e1 t1 typ1 typ2 n1,
  degree_Typ_wrt_Typ n1 t1 ->
  typ1 <> typ2 ->
  typ2 `notin` tt_fv_Typ t1 ->
  t_subst_Exp t1 typ1 (close_Exp_wrt_Typ_rec n1 typ2 e1) = close_Exp_wrt_Typ_rec n1 typ2 (t_subst_Exp t1 typ1 e1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Exp_close_Exp_wrt_Typ_rec :
forall e1 t1 typ1 typ2 n1,
  degree_Typ_wrt_Typ n1 t1 ->
  typ1 <> typ2 ->
  typ2 `notin` tt_fv_Typ t1 ->
  t_subst_Exp t1 typ1 (close_Exp_wrt_Typ_rec n1 typ2 e1) = close_Exp_wrt_Typ_rec n1 typ2 (t_subst_Exp t1 typ1 e1).
Proof. Admitted.

Hint Resolve t_subst_Exp_close_Exp_wrt_Typ_rec : lngen.

Lemma t_subst_Typ_close_Typ_wrt_Typ :
forall t2 t1 typ1 typ2,
  lc_Typ t1 ->  typ1 <> typ2 ->
  typ2 `notin` tt_fv_Typ t1 ->
  t_subst_Typ t1 typ1 (close_Typ_wrt_Typ typ2 t2) = close_Typ_wrt_Typ typ2 (t_subst_Typ t1 typ1 t2).
Proof. Admitted.

Hint Resolve t_subst_Typ_close_Typ_wrt_Typ : lngen.

Lemma e_subst_Exp_close_Exp_wrt_Exp :
forall e2 e1 x1 x2,
  lc_Exp e1 ->  x1 <> x2 ->
  x2 `notin` e_fv_Exp e1 ->
  e_subst_Exp e1 x1 (close_Exp_wrt_Exp x2 e2) = close_Exp_wrt_Exp x2 (e_subst_Exp e1 x1 e2).
Proof. Admitted.

Hint Resolve e_subst_Exp_close_Exp_wrt_Exp : lngen.

Lemma e_subst_Exp_close_Exp_wrt_Typ :
forall e2 e1 typ1 x1,
  lc_Exp e1 ->  x1 `notin` tt_fv_Exp e1 ->
  e_subst_Exp e1 typ1 (close_Exp_wrt_Typ x1 e2) = close_Exp_wrt_Typ x1 (e_subst_Exp e1 typ1 e2).
Proof. Admitted.

Hint Resolve e_subst_Exp_close_Exp_wrt_Typ : lngen.

Lemma t_subst_Exp_close_Exp_wrt_Exp :
forall e1 t1 x1 typ1,
  lc_Typ t1 ->  t_subst_Exp t1 x1 (close_Exp_wrt_Exp typ1 e1) = close_Exp_wrt_Exp typ1 (t_subst_Exp t1 x1 e1).
Proof. Admitted.

Hint Resolve t_subst_Exp_close_Exp_wrt_Exp : lngen.

Lemma t_subst_Exp_close_Exp_wrt_Typ :
forall e1 t1 typ1 typ2,
  lc_Typ t1 ->  typ1 <> typ2 ->
  typ2 `notin` tt_fv_Typ t1 ->
  t_subst_Exp t1 typ1 (close_Exp_wrt_Typ typ2 e1) = close_Exp_wrt_Typ typ2 (t_subst_Exp t1 typ1 e1).
Proof. Admitted.

Hint Resolve t_subst_Exp_close_Exp_wrt_Typ : lngen.

(* begin hide *)

Lemma t_subst_Typ_degree_Typ_wrt_Typ_mutual :
(forall t1 t2 typ1 n1,
  degree_Typ_wrt_Typ n1 t1 ->
  degree_Typ_wrt_Typ n1 t2 ->
  degree_Typ_wrt_Typ n1 (t_subst_Typ t2 typ1 t1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Typ_degree_Typ_wrt_Typ :
forall t1 t2 typ1 n1,
  degree_Typ_wrt_Typ n1 t1 ->
  degree_Typ_wrt_Typ n1 t2 ->
  degree_Typ_wrt_Typ n1 (t_subst_Typ t2 typ1 t1).
Proof. Admitted.

Hint Resolve t_subst_Typ_degree_Typ_wrt_Typ : lngen.

(* begin hide *)

Lemma e_subst_Exp_degree_Exp_wrt_Exp_mutual :
(forall e1 e2 x1 n1,
  degree_Exp_wrt_Exp n1 e1 ->
  degree_Exp_wrt_Exp n1 e2 ->
  degree_Exp_wrt_Exp n1 (e_subst_Exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_Exp_degree_Exp_wrt_Exp :
forall e1 e2 x1 n1,
  degree_Exp_wrt_Exp n1 e1 ->
  degree_Exp_wrt_Exp n1 e2 ->
  degree_Exp_wrt_Exp n1 (e_subst_Exp e2 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_Exp_degree_Exp_wrt_Exp : lngen.

(* begin hide *)

Lemma e_subst_Exp_degree_Exp_wrt_Typ_mutual :
(forall e1 e2 x1 n1,
  degree_Exp_wrt_Typ n1 e1 ->
  degree_Exp_wrt_Typ n1 e2 ->
  degree_Exp_wrt_Typ n1 (e_subst_Exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_Exp_degree_Exp_wrt_Typ :
forall e1 e2 x1 n1,
  degree_Exp_wrt_Typ n1 e1 ->
  degree_Exp_wrt_Typ n1 e2 ->
  degree_Exp_wrt_Typ n1 (e_subst_Exp e2 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_Exp_degree_Exp_wrt_Typ : lngen.

(* begin hide *)

Lemma t_subst_Exp_degree_Exp_wrt_Exp_mutual :
(forall e1 t1 typ1 n1,
  degree_Exp_wrt_Exp n1 e1 ->
  degree_Exp_wrt_Exp n1 (t_subst_Exp t1 typ1 e1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Exp_degree_Exp_wrt_Exp :
forall e1 t1 typ1 n1,
  degree_Exp_wrt_Exp n1 e1 ->
  degree_Exp_wrt_Exp n1 (t_subst_Exp t1 typ1 e1).
Proof. Admitted.

Hint Resolve t_subst_Exp_degree_Exp_wrt_Exp : lngen.

(* begin hide *)

Lemma t_subst_Exp_degree_Exp_wrt_Typ_mutual :
(forall e1 t1 typ1 n1,
  degree_Exp_wrt_Typ n1 e1 ->
  degree_Typ_wrt_Typ n1 t1 ->
  degree_Exp_wrt_Typ n1 (t_subst_Exp t1 typ1 e1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Exp_degree_Exp_wrt_Typ :
forall e1 t1 typ1 n1,
  degree_Exp_wrt_Typ n1 e1 ->
  degree_Typ_wrt_Typ n1 t1 ->
  degree_Exp_wrt_Typ n1 (t_subst_Exp t1 typ1 e1).
Proof. Admitted.

Hint Resolve t_subst_Exp_degree_Exp_wrt_Typ : lngen.

(* begin hide *)

Lemma t_subst_Typ_fresh_eq_mutual :
(forall t2 t1 typ1,
  typ1 `notin` tt_fv_Typ t2 ->
  t_subst_Typ t1 typ1 t2 = t2).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Typ_fresh_eq :
forall t2 t1 typ1,
  typ1 `notin` tt_fv_Typ t2 ->
  t_subst_Typ t1 typ1 t2 = t2.
Proof. Admitted.

Hint Resolve t_subst_Typ_fresh_eq : lngen.
Hint Rewrite t_subst_Typ_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma e_subst_Exp_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` e_fv_Exp e2 ->
  e_subst_Exp e1 x1 e2 = e2).
Proof. Admitted.

(* end hide *)

Lemma e_subst_Exp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` e_fv_Exp e2 ->
  e_subst_Exp e1 x1 e2 = e2.
Proof. Admitted.

Hint Resolve e_subst_Exp_fresh_eq : lngen.
Hint Rewrite e_subst_Exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma t_subst_Exp_fresh_eq_mutual :
(forall e1 t1 typ1,
  typ1 `notin` tt_fv_Exp e1 ->
  t_subst_Exp t1 typ1 e1 = e1).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Exp_fresh_eq :
forall e1 t1 typ1,
  typ1 `notin` tt_fv_Exp e1 ->
  t_subst_Exp t1 typ1 e1 = e1.
Proof. Admitted.

Hint Resolve t_subst_Exp_fresh_eq : lngen.
Hint Rewrite t_subst_Exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma t_subst_Typ_fresh_same_mutual :
(forall t2 t1 typ1,
  typ1 `notin` tt_fv_Typ t1 ->
  typ1 `notin` tt_fv_Typ (t_subst_Typ t1 typ1 t2)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Typ_fresh_same :
forall t2 t1 typ1,
  typ1 `notin` tt_fv_Typ t1 ->
  typ1 `notin` tt_fv_Typ (t_subst_Typ t1 typ1 t2).
Proof. Admitted.

Hint Resolve t_subst_Typ_fresh_same : lngen.

(* begin hide *)

Lemma e_subst_Exp_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` e_fv_Exp e1 ->
  x1 `notin` e_fv_Exp (e_subst_Exp e1 x1 e2)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_Exp_fresh_same :
forall e2 e1 x1,
  x1 `notin` e_fv_Exp e1 ->
  x1 `notin` e_fv_Exp (e_subst_Exp e1 x1 e2).
Proof. Admitted.

Hint Resolve e_subst_Exp_fresh_same : lngen.

(* begin hide *)

Lemma t_subst_Exp_fresh_same_mutual :
(forall e1 t1 typ1,
  typ1 `notin` tt_fv_Typ t1 ->
  typ1 `notin` tt_fv_Exp (t_subst_Exp t1 typ1 e1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Exp_fresh_same :
forall e1 t1 typ1,
  typ1 `notin` tt_fv_Typ t1 ->
  typ1 `notin` tt_fv_Exp (t_subst_Exp t1 typ1 e1).
Proof. Admitted.

Hint Resolve t_subst_Exp_fresh_same : lngen.

(* begin hide *)

Lemma t_subst_Typ_fresh_mutual :
(forall t2 t1 typ1 typ2,
  typ1 `notin` tt_fv_Typ t2 ->
  typ1 `notin` tt_fv_Typ t1 ->
  typ1 `notin` tt_fv_Typ (t_subst_Typ t1 typ2 t2)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Typ_fresh :
forall t2 t1 typ1 typ2,
  typ1 `notin` tt_fv_Typ t2 ->
  typ1 `notin` tt_fv_Typ t1 ->
  typ1 `notin` tt_fv_Typ (t_subst_Typ t1 typ2 t2).
Proof. Admitted.

Hint Resolve t_subst_Typ_fresh : lngen.

(* begin hide *)

Lemma e_subst_Exp_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` e_fv_Exp e2 ->
  x1 `notin` e_fv_Exp e1 ->
  x1 `notin` e_fv_Exp (e_subst_Exp e1 x2 e2)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_Exp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` e_fv_Exp e2 ->
  x1 `notin` e_fv_Exp e1 ->
  x1 `notin` e_fv_Exp (e_subst_Exp e1 x2 e2).
Proof. Admitted.

Hint Resolve e_subst_Exp_fresh : lngen.

(* begin hide *)

Lemma t_subst_Exp_fresh_mutual :
(forall e1 t1 typ1 typ2,
  typ1 `notin` tt_fv_Exp e1 ->
  typ1 `notin` tt_fv_Typ t1 ->
  typ1 `notin` tt_fv_Exp (t_subst_Exp t1 typ2 e1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Exp_fresh :
forall e1 t1 typ1 typ2,
  typ1 `notin` tt_fv_Exp e1 ->
  typ1 `notin` tt_fv_Typ t1 ->
  typ1 `notin` tt_fv_Exp (t_subst_Exp t1 typ2 e1).
Proof. Admitted.

Hint Resolve t_subst_Exp_fresh : lngen.

Lemma t_subst_Typ_lc_Typ :
forall t1 t2 typ1,
  lc_Typ t1 ->
  lc_Typ t2 ->
  lc_Typ (t_subst_Typ t2 typ1 t1).
Proof. Admitted.

Hint Resolve t_subst_Typ_lc_Typ : lngen.

Lemma e_subst_Exp_lc_Exp :
forall e1 e2 x1,
  lc_Exp e1 ->
  lc_Exp e2 ->
  lc_Exp (e_subst_Exp e2 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_Exp_lc_Exp : lngen.

Lemma t_subst_Exp_lc_Exp :
forall e1 t1 typ1,
  lc_Exp e1 ->
  lc_Typ t1 ->
  lc_Exp (t_subst_Exp t1 typ1 e1).
Proof. Admitted.

Hint Resolve t_subst_Exp_lc_Exp : lngen.

(* begin hide *)

Lemma t_subst_Typ_open_Typ_wrt_Typ_rec_mutual :
(forall t3 t1 t2 typ1 n1,
  lc_Typ t1 ->
  t_subst_Typ t1 typ1 (open_Typ_wrt_Typ_rec n1 t2 t3) = open_Typ_wrt_Typ_rec n1 (t_subst_Typ t1 typ1 t2) (t_subst_Typ t1 typ1 t3)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_Typ_open_Typ_wrt_Typ_rec :
forall t3 t1 t2 typ1 n1,
  lc_Typ t1 ->
  t_subst_Typ t1 typ1 (open_Typ_wrt_Typ_rec n1 t2 t3) = open_Typ_wrt_Typ_rec n1 (t_subst_Typ t1 typ1 t2) (t_subst_Typ t1 typ1 t3).
Proof. Admitted.

Hint Resolve t_subst_Typ_open_Typ_wrt_Typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_Exp_open_Exp_wrt_Exp_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_Exp e1 ->
  e_subst_Exp e1 x1 (open_Exp_wrt_Exp_rec n1 e2 e3) = open_Exp_wrt_Exp_rec n1 (e_subst_Exp e1 x1 e2) (e_subst_Exp e1 x1 e3)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_subst_Exp_open_Exp_wrt_Exp_rec :
forall e3 e1 e2 x1 n1,
  lc_Exp e1 ->
  e_subst_Exp e1 x1 (open_Exp_wrt_Exp_rec n1 e2 e3) = open_Exp_wrt_Exp_rec n1 (e_subst_Exp e1 x1 e2) (e_subst_Exp e1 x1 e3).
Proof. Admitted.

Hint Resolve e_subst_Exp_open_Exp_wrt_Exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_Exp_open_Exp_wrt_Typ_rec_mutual :
(forall e2 e1 t1 x1 n1,
  lc_Exp e1 ->
  e_subst_Exp e1 x1 (open_Exp_wrt_Typ_rec n1 t1 e2) = open_Exp_wrt_Typ_rec n1 t1 (e_subst_Exp e1 x1 e2)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_subst_Exp_open_Exp_wrt_Typ_rec :
forall e2 e1 t1 x1 n1,
  lc_Exp e1 ->
  e_subst_Exp e1 x1 (open_Exp_wrt_Typ_rec n1 t1 e2) = open_Exp_wrt_Typ_rec n1 t1 (e_subst_Exp e1 x1 e2).
Proof. Admitted.

Hint Resolve e_subst_Exp_open_Exp_wrt_Typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_Exp_open_Exp_wrt_Exp_rec_mutual :
(forall e2 t1 e1 typ1 n1,
  t_subst_Exp t1 typ1 (open_Exp_wrt_Exp_rec n1 e1 e2) = open_Exp_wrt_Exp_rec n1 (t_subst_Exp t1 typ1 e1) (t_subst_Exp t1 typ1 e2)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_Exp_open_Exp_wrt_Exp_rec :
forall e2 t1 e1 typ1 n1,
  t_subst_Exp t1 typ1 (open_Exp_wrt_Exp_rec n1 e1 e2) = open_Exp_wrt_Exp_rec n1 (t_subst_Exp t1 typ1 e1) (t_subst_Exp t1 typ1 e2).
Proof. Admitted.

Hint Resolve t_subst_Exp_open_Exp_wrt_Exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_Exp_open_Exp_wrt_Typ_rec_mutual :
(forall e1 t1 t2 typ1 n1,
  lc_Typ t1 ->
  t_subst_Exp t1 typ1 (open_Exp_wrt_Typ_rec n1 t2 e1) = open_Exp_wrt_Typ_rec n1 (t_subst_Typ t1 typ1 t2) (t_subst_Exp t1 typ1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_Exp_open_Exp_wrt_Typ_rec :
forall e1 t1 t2 typ1 n1,
  lc_Typ t1 ->
  t_subst_Exp t1 typ1 (open_Exp_wrt_Typ_rec n1 t2 e1) = open_Exp_wrt_Typ_rec n1 (t_subst_Typ t1 typ1 t2) (t_subst_Exp t1 typ1 e1).
Proof. Admitted.

Hint Resolve t_subst_Exp_open_Exp_wrt_Typ_rec : lngen.

(* end hide *)

Lemma t_subst_Typ_open_Typ_wrt_Typ :
forall t3 t1 t2 typ1,
  lc_Typ t1 ->
  t_subst_Typ t1 typ1 (open_Typ_wrt_Typ t3 t2) = open_Typ_wrt_Typ (t_subst_Typ t1 typ1 t3) (t_subst_Typ t1 typ1 t2).
Proof. Admitted.

Hint Resolve t_subst_Typ_open_Typ_wrt_Typ : lngen.

Lemma e_subst_Exp_open_Exp_wrt_Exp :
forall e3 e1 e2 x1,
  lc_Exp e1 ->
  e_subst_Exp e1 x1 (open_Exp_wrt_Exp e3 e2) = open_Exp_wrt_Exp (e_subst_Exp e1 x1 e3) (e_subst_Exp e1 x1 e2).
Proof. Admitted.

Hint Resolve e_subst_Exp_open_Exp_wrt_Exp : lngen.

Lemma e_subst_Exp_open_Exp_wrt_Typ :
forall e2 e1 t1 x1,
  lc_Exp e1 ->
  e_subst_Exp e1 x1 (open_Exp_wrt_Typ e2 t1) = open_Exp_wrt_Typ (e_subst_Exp e1 x1 e2) t1.
Proof. Admitted.

Hint Resolve e_subst_Exp_open_Exp_wrt_Typ : lngen.

Lemma t_subst_Exp_open_Exp_wrt_Exp :
forall e2 t1 e1 typ1,
  t_subst_Exp t1 typ1 (open_Exp_wrt_Exp e2 e1) = open_Exp_wrt_Exp (t_subst_Exp t1 typ1 e2) (t_subst_Exp t1 typ1 e1).
Proof. Admitted.

Hint Resolve t_subst_Exp_open_Exp_wrt_Exp : lngen.

Lemma t_subst_Exp_open_Exp_wrt_Typ :
forall e1 t1 t2 typ1,
  lc_Typ t1 ->
  t_subst_Exp t1 typ1 (open_Exp_wrt_Typ e1 t2) = open_Exp_wrt_Typ (t_subst_Exp t1 typ1 e1) (t_subst_Typ t1 typ1 t2).
Proof. Admitted.

Hint Resolve t_subst_Exp_open_Exp_wrt_Typ : lngen.

Lemma t_subst_Typ_open_Typ_wrt_Typ_var :
forall t2 t1 typ1 typ2,
  typ1 <> typ2 ->
  lc_Typ t1 ->
  open_Typ_wrt_Typ (t_subst_Typ t1 typ1 t2) (t_var_f typ2) = t_subst_Typ t1 typ1 (open_Typ_wrt_Typ t2 (t_var_f typ2)).
Proof. Admitted.

Hint Resolve t_subst_Typ_open_Typ_wrt_Typ_var : lngen.

Lemma e_subst_Exp_open_Exp_wrt_Exp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_Exp e1 ->
  open_Exp_wrt_Exp (e_subst_Exp e1 x1 e2) (e_var_f x2) = e_subst_Exp e1 x1 (open_Exp_wrt_Exp e2 (e_var_f x2)).
Proof. Admitted.

Hint Resolve e_subst_Exp_open_Exp_wrt_Exp_var : lngen.

Lemma e_subst_Exp_open_Exp_wrt_Typ_var :
forall e2 e1 x1 typ1,
  lc_Exp e1 ->
  open_Exp_wrt_Typ (e_subst_Exp e1 x1 e2) (t_var_f typ1) = e_subst_Exp e1 x1 (open_Exp_wrt_Typ e2 (t_var_f typ1)).
Proof. Admitted.

Hint Resolve e_subst_Exp_open_Exp_wrt_Typ_var : lngen.

Lemma t_subst_Exp_open_Exp_wrt_Exp_var :
forall e1 t1 typ1 x1,
  open_Exp_wrt_Exp (t_subst_Exp t1 typ1 e1) (e_var_f x1) = t_subst_Exp t1 typ1 (open_Exp_wrt_Exp e1 (e_var_f x1)).
Proof. Admitted.

Hint Resolve t_subst_Exp_open_Exp_wrt_Exp_var : lngen.

Lemma t_subst_Exp_open_Exp_wrt_Typ_var :
forall e1 t1 typ1 typ2,
  typ1 <> typ2 ->
  lc_Typ t1 ->
  open_Exp_wrt_Typ (t_subst_Exp t1 typ1 e1) (t_var_f typ2) = t_subst_Exp t1 typ1 (open_Exp_wrt_Typ e1 (t_var_f typ2)).
Proof. Admitted.

Hint Resolve t_subst_Exp_open_Exp_wrt_Typ_var : lngen.

(* begin hide *)

Lemma t_subst_Typ_spec_rec_mutual :
(forall t1 t2 typ1 n1,
  t_subst_Typ t2 typ1 t1 = open_Typ_wrt_Typ_rec n1 t2 (close_Typ_wrt_Typ_rec n1 typ1 t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_Typ_spec_rec :
forall t1 t2 typ1 n1,
  t_subst_Typ t2 typ1 t1 = open_Typ_wrt_Typ_rec n1 t2 (close_Typ_wrt_Typ_rec n1 typ1 t1).
Proof. Admitted.

Hint Resolve t_subst_Typ_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_Exp_spec_rec_mutual :
(forall e1 e2 x1 n1,
  e_subst_Exp e2 x1 e1 = open_Exp_wrt_Exp_rec n1 e2 (close_Exp_wrt_Exp_rec n1 x1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_subst_Exp_spec_rec :
forall e1 e2 x1 n1,
  e_subst_Exp e2 x1 e1 = open_Exp_wrt_Exp_rec n1 e2 (close_Exp_wrt_Exp_rec n1 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_Exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_Exp_spec_rec_mutual :
(forall e1 t1 typ1 n1,
  t_subst_Exp t1 typ1 e1 = open_Exp_wrt_Typ_rec n1 t1 (close_Exp_wrt_Typ_rec n1 typ1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_Exp_spec_rec :
forall e1 t1 typ1 n1,
  t_subst_Exp t1 typ1 e1 = open_Exp_wrt_Typ_rec n1 t1 (close_Exp_wrt_Typ_rec n1 typ1 e1).
Proof. Admitted.

Hint Resolve t_subst_Exp_spec_rec : lngen.

(* end hide *)

Lemma t_subst_Typ_spec :
forall t1 t2 typ1,
  t_subst_Typ t2 typ1 t1 = open_Typ_wrt_Typ (close_Typ_wrt_Typ typ1 t1) t2.
Proof. Admitted.

Hint Resolve t_subst_Typ_spec : lngen.

Lemma e_subst_Exp_spec :
forall e1 e2 x1,
  e_subst_Exp e2 x1 e1 = open_Exp_wrt_Exp (close_Exp_wrt_Exp x1 e1) e2.
Proof. Admitted.

Hint Resolve e_subst_Exp_spec : lngen.

Lemma t_subst_Exp_spec :
forall e1 t1 typ1,
  t_subst_Exp t1 typ1 e1 = open_Exp_wrt_Typ (close_Exp_wrt_Typ typ1 e1) t1.
Proof. Admitted.

Hint Resolve t_subst_Exp_spec : lngen.

(* begin hide *)

Lemma t_subst_Typ_t_subst_Typ_mutual :
(forall t1 t2 t3 typ2 typ1,
  typ2 `notin` tt_fv_Typ t2 ->
  typ2 <> typ1 ->
  t_subst_Typ t2 typ1 (t_subst_Typ t3 typ2 t1) = t_subst_Typ (t_subst_Typ t2 typ1 t3) typ2 (t_subst_Typ t2 typ1 t1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Typ_t_subst_Typ :
forall t1 t2 t3 typ2 typ1,
  typ2 `notin` tt_fv_Typ t2 ->
  typ2 <> typ1 ->
  t_subst_Typ t2 typ1 (t_subst_Typ t3 typ2 t1) = t_subst_Typ (t_subst_Typ t2 typ1 t3) typ2 (t_subst_Typ t2 typ1 t1).
Proof. Admitted.

Hint Resolve t_subst_Typ_t_subst_Typ : lngen.

(* begin hide *)

Lemma e_subst_Exp_e_subst_Exp_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` e_fv_Exp e2 ->
  x2 <> x1 ->
  e_subst_Exp e2 x1 (e_subst_Exp e3 x2 e1) = e_subst_Exp (e_subst_Exp e2 x1 e3) x2 (e_subst_Exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_Exp_e_subst_Exp :
forall e1 e2 e3 x2 x1,
  x2 `notin` e_fv_Exp e2 ->
  x2 <> x1 ->
  e_subst_Exp e2 x1 (e_subst_Exp e3 x2 e1) = e_subst_Exp (e_subst_Exp e2 x1 e3) x2 (e_subst_Exp e2 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_Exp_e_subst_Exp : lngen.

(* begin hide *)

Lemma e_subst_Exp_t_subst_Exp_mutual :
(forall e1 e2 t1 typ1 x1,
  typ1 `notin` tt_fv_Exp e2 ->
  e_subst_Exp e2 x1 (t_subst_Exp t1 typ1 e1) = t_subst_Exp t1 typ1 (e_subst_Exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_Exp_t_subst_Exp :
forall e1 e2 t1 typ1 x1,
  typ1 `notin` tt_fv_Exp e2 ->
  e_subst_Exp e2 x1 (t_subst_Exp t1 typ1 e1) = t_subst_Exp t1 typ1 (e_subst_Exp e2 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_Exp_t_subst_Exp : lngen.

(* begin hide *)

Lemma t_subst_Exp_e_subst_Exp_mutual :
(forall e1 t1 e2 x1 typ1,
  t_subst_Exp t1 typ1 (e_subst_Exp e2 x1 e1) = e_subst_Exp (t_subst_Exp t1 typ1 e2) x1 (t_subst_Exp t1 typ1 e1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Exp_e_subst_Exp :
forall e1 t1 e2 x1 typ1,
  t_subst_Exp t1 typ1 (e_subst_Exp e2 x1 e1) = e_subst_Exp (t_subst_Exp t1 typ1 e2) x1 (t_subst_Exp t1 typ1 e1).
Proof. Admitted.

Hint Resolve t_subst_Exp_e_subst_Exp : lngen.

(* begin hide *)

Lemma t_subst_Exp_t_subst_Exp_mutual :
(forall e1 t1 t2 typ2 typ1,
  typ2 `notin` tt_fv_Typ t1 ->
  typ2 <> typ1 ->
  t_subst_Exp t1 typ1 (t_subst_Exp t2 typ2 e1) = t_subst_Exp (t_subst_Typ t1 typ1 t2) typ2 (t_subst_Exp t1 typ1 e1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Exp_t_subst_Exp :
forall e1 t1 t2 typ2 typ1,
  typ2 `notin` tt_fv_Typ t1 ->
  typ2 <> typ1 ->
  t_subst_Exp t1 typ1 (t_subst_Exp t2 typ2 e1) = t_subst_Exp (t_subst_Typ t1 typ1 t2) typ2 (t_subst_Exp t1 typ1 e1).
Proof. Admitted.

Hint Resolve t_subst_Exp_t_subst_Exp : lngen.

(* begin hide *)

Lemma t_subst_Typ_close_Typ_wrt_Typ_rec_open_Typ_wrt_Typ_rec_mutual :
(forall t2 t1 typ1 typ2 n1,
  typ2 `notin` tt_fv_Typ t2 ->
  typ2 `notin` tt_fv_Typ t1 ->
  typ2 <> typ1 ->
  degree_Typ_wrt_Typ n1 t1 ->
  t_subst_Typ t1 typ1 t2 = close_Typ_wrt_Typ_rec n1 typ2 (t_subst_Typ t1 typ1 (open_Typ_wrt_Typ_rec n1 (t_var_f typ2) t2))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_Typ_close_Typ_wrt_Typ_rec_open_Typ_wrt_Typ_rec :
forall t2 t1 typ1 typ2 n1,
  typ2 `notin` tt_fv_Typ t2 ->
  typ2 `notin` tt_fv_Typ t1 ->
  typ2 <> typ1 ->
  degree_Typ_wrt_Typ n1 t1 ->
  t_subst_Typ t1 typ1 t2 = close_Typ_wrt_Typ_rec n1 typ2 (t_subst_Typ t1 typ1 (open_Typ_wrt_Typ_rec n1 (t_var_f typ2) t2)).
Proof. Admitted.

Hint Resolve t_subst_Typ_close_Typ_wrt_Typ_rec_open_Typ_wrt_Typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_Exp_close_Exp_wrt_Exp_rec_open_Exp_wrt_Exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` e_fv_Exp e2 ->
  x2 `notin` e_fv_Exp e1 ->
  x2 <> x1 ->
  degree_Exp_wrt_Exp n1 e1 ->
  e_subst_Exp e1 x1 e2 = close_Exp_wrt_Exp_rec n1 x2 (e_subst_Exp e1 x1 (open_Exp_wrt_Exp_rec n1 (e_var_f x2) e2))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_subst_Exp_close_Exp_wrt_Exp_rec_open_Exp_wrt_Exp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` e_fv_Exp e2 ->
  x2 `notin` e_fv_Exp e1 ->
  x2 <> x1 ->
  degree_Exp_wrt_Exp n1 e1 ->
  e_subst_Exp e1 x1 e2 = close_Exp_wrt_Exp_rec n1 x2 (e_subst_Exp e1 x1 (open_Exp_wrt_Exp_rec n1 (e_var_f x2) e2)).
Proof. Admitted.

Hint Resolve e_subst_Exp_close_Exp_wrt_Exp_rec_open_Exp_wrt_Exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_Exp_close_Exp_wrt_Typ_rec_open_Exp_wrt_Typ_rec_mutual :
(forall e2 e1 x1 typ1 n1,
  typ1 `notin` tt_fv_Exp e2 ->
  typ1 `notin` tt_fv_Exp e1 ->
  degree_Exp_wrt_Typ n1 e1 ->
  e_subst_Exp e1 x1 e2 = close_Exp_wrt_Typ_rec n1 typ1 (e_subst_Exp e1 x1 (open_Exp_wrt_Typ_rec n1 (t_var_f typ1) e2))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_subst_Exp_close_Exp_wrt_Typ_rec_open_Exp_wrt_Typ_rec :
forall e2 e1 x1 typ1 n1,
  typ1 `notin` tt_fv_Exp e2 ->
  typ1 `notin` tt_fv_Exp e1 ->
  degree_Exp_wrt_Typ n1 e1 ->
  e_subst_Exp e1 x1 e2 = close_Exp_wrt_Typ_rec n1 typ1 (e_subst_Exp e1 x1 (open_Exp_wrt_Typ_rec n1 (t_var_f typ1) e2)).
Proof. Admitted.

Hint Resolve e_subst_Exp_close_Exp_wrt_Typ_rec_open_Exp_wrt_Typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_Exp_close_Exp_wrt_Exp_rec_open_Exp_wrt_Exp_rec_mutual :
(forall e1 t1 typ1 x1 n1,
  x1 `notin` e_fv_Exp e1 ->
  t_subst_Exp t1 typ1 e1 = close_Exp_wrt_Exp_rec n1 x1 (t_subst_Exp t1 typ1 (open_Exp_wrt_Exp_rec n1 (e_var_f x1) e1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_Exp_close_Exp_wrt_Exp_rec_open_Exp_wrt_Exp_rec :
forall e1 t1 typ1 x1 n1,
  x1 `notin` e_fv_Exp e1 ->
  t_subst_Exp t1 typ1 e1 = close_Exp_wrt_Exp_rec n1 x1 (t_subst_Exp t1 typ1 (open_Exp_wrt_Exp_rec n1 (e_var_f x1) e1)).
Proof. Admitted.

Hint Resolve t_subst_Exp_close_Exp_wrt_Exp_rec_open_Exp_wrt_Exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_Exp_close_Exp_wrt_Typ_rec_open_Exp_wrt_Typ_rec_mutual :
(forall e1 t1 typ1 typ2 n1,
  typ2 `notin` tt_fv_Exp e1 ->
  typ2 `notin` tt_fv_Typ t1 ->
  typ2 <> typ1 ->
  degree_Typ_wrt_Typ n1 t1 ->
  t_subst_Exp t1 typ1 e1 = close_Exp_wrt_Typ_rec n1 typ2 (t_subst_Exp t1 typ1 (open_Exp_wrt_Typ_rec n1 (t_var_f typ2) e1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_Exp_close_Exp_wrt_Typ_rec_open_Exp_wrt_Typ_rec :
forall e1 t1 typ1 typ2 n1,
  typ2 `notin` tt_fv_Exp e1 ->
  typ2 `notin` tt_fv_Typ t1 ->
  typ2 <> typ1 ->
  degree_Typ_wrt_Typ n1 t1 ->
  t_subst_Exp t1 typ1 e1 = close_Exp_wrt_Typ_rec n1 typ2 (t_subst_Exp t1 typ1 (open_Exp_wrt_Typ_rec n1 (t_var_f typ2) e1)).
Proof. Admitted.

Hint Resolve t_subst_Exp_close_Exp_wrt_Typ_rec_open_Exp_wrt_Typ_rec : lngen.

(* end hide *)

Lemma t_subst_Typ_close_Typ_wrt_Typ_open_Typ_wrt_Typ :
forall t2 t1 typ1 typ2,
  typ2 `notin` tt_fv_Typ t2 ->
  typ2 `notin` tt_fv_Typ t1 ->
  typ2 <> typ1 ->
  lc_Typ t1 ->
  t_subst_Typ t1 typ1 t2 = close_Typ_wrt_Typ typ2 (t_subst_Typ t1 typ1 (open_Typ_wrt_Typ t2 (t_var_f typ2))).
Proof. Admitted.

Hint Resolve t_subst_Typ_close_Typ_wrt_Typ_open_Typ_wrt_Typ : lngen.

Lemma e_subst_Exp_close_Exp_wrt_Exp_open_Exp_wrt_Exp :
forall e2 e1 x1 x2,
  x2 `notin` e_fv_Exp e2 ->
  x2 `notin` e_fv_Exp e1 ->
  x2 <> x1 ->
  lc_Exp e1 ->
  e_subst_Exp e1 x1 e2 = close_Exp_wrt_Exp x2 (e_subst_Exp e1 x1 (open_Exp_wrt_Exp e2 (e_var_f x2))).
Proof. Admitted.

Hint Resolve e_subst_Exp_close_Exp_wrt_Exp_open_Exp_wrt_Exp : lngen.

Lemma e_subst_Exp_close_Exp_wrt_Typ_open_Exp_wrt_Typ :
forall e2 e1 x1 typ1,
  typ1 `notin` tt_fv_Exp e2 ->
  typ1 `notin` tt_fv_Exp e1 ->
  lc_Exp e1 ->
  e_subst_Exp e1 x1 e2 = close_Exp_wrt_Typ typ1 (e_subst_Exp e1 x1 (open_Exp_wrt_Typ e2 (t_var_f typ1))).
Proof. Admitted.

Hint Resolve e_subst_Exp_close_Exp_wrt_Typ_open_Exp_wrt_Typ : lngen.

Lemma t_subst_Exp_close_Exp_wrt_Exp_open_Exp_wrt_Exp :
forall e1 t1 typ1 x1,
  x1 `notin` e_fv_Exp e1 ->
  lc_Typ t1 ->
  t_subst_Exp t1 typ1 e1 = close_Exp_wrt_Exp x1 (t_subst_Exp t1 typ1 (open_Exp_wrt_Exp e1 (e_var_f x1))).
Proof. Admitted.

Hint Resolve t_subst_Exp_close_Exp_wrt_Exp_open_Exp_wrt_Exp : lngen.

Lemma t_subst_Exp_close_Exp_wrt_Typ_open_Exp_wrt_Typ :
forall e1 t1 typ1 typ2,
  typ2 `notin` tt_fv_Exp e1 ->
  typ2 `notin` tt_fv_Typ t1 ->
  typ2 <> typ1 ->
  lc_Typ t1 ->
  t_subst_Exp t1 typ1 e1 = close_Exp_wrt_Typ typ2 (t_subst_Exp t1 typ1 (open_Exp_wrt_Typ e1 (t_var_f typ2))).
Proof. Admitted.

Hint Resolve t_subst_Exp_close_Exp_wrt_Typ_open_Exp_wrt_Typ : lngen.

Lemma t_subst_Typ_t_all :
forall typ2 t2 t1 typ1,
  lc_Typ t1 ->
  typ2 `notin` tt_fv_Typ t1 `union` tt_fv_Typ t2 `union` singleton typ1 ->
  t_subst_Typ t1 typ1 (t_all t2) = t_all (close_Typ_wrt_Typ typ2 (t_subst_Typ t1 typ1 (open_Typ_wrt_Typ t2 (t_var_f typ2)))).
Proof. Admitted.

Hint Resolve t_subst_Typ_t_all : lngen.

Lemma e_subst_Exp_e_lam :
forall x2 t1 e2 e1 x1,
  lc_Exp e1 ->
  x2 `notin` e_fv_Exp e1 `union` e_fv_Exp e2 `union` singleton x1 ->
  e_subst_Exp e1 x1 (e_lam t1 e2) = e_lam (t1) (close_Exp_wrt_Exp x2 (e_subst_Exp e1 x1 (open_Exp_wrt_Exp e2 (e_var_f x2)))).
Proof. Admitted.

Hint Resolve e_subst_Exp_e_lam : lngen.

Lemma e_subst_Exp_e_Lam :
forall typ1 e2 e1 x1,
  lc_Exp e1 ->
  typ1 `notin` tt_fv_Exp e1 `union` tt_fv_Exp e2 ->
  e_subst_Exp e1 x1 (e_Lam e2) = e_Lam (close_Exp_wrt_Typ typ1 (e_subst_Exp e1 x1 (open_Exp_wrt_Typ e2 (t_var_f typ1)))).
Proof. Admitted.

Hint Resolve e_subst_Exp_e_Lam : lngen.

Lemma t_subst_Exp_e_lam :
forall x1 t2 e1 t1 typ1,
  lc_Typ t1 ->
  x1 `notin` e_fv_Exp e1 ->
  t_subst_Exp t1 typ1 (e_lam t2 e1) = e_lam (t_subst_Typ t1 typ1 t2) (close_Exp_wrt_Exp x1 (t_subst_Exp t1 typ1 (open_Exp_wrt_Exp e1 (e_var_f x1)))).
Proof. Admitted.

Hint Resolve t_subst_Exp_e_lam : lngen.

Lemma t_subst_Exp_e_Lam :
forall typ2 e1 t1 typ1,
  lc_Typ t1 ->
  typ2 `notin` tt_fv_Typ t1 `union` tt_fv_Exp e1 `union` singleton typ1 ->
  t_subst_Exp t1 typ1 (e_Lam e1) = e_Lam (close_Exp_wrt_Typ typ2 (t_subst_Exp t1 typ1 (open_Exp_wrt_Typ e1 (t_var_f typ2)))).
Proof. Admitted.

Hint Resolve t_subst_Exp_e_Lam : lngen.

(* begin hide *)

Lemma t_subst_Typ_intro_rec_mutual :
(forall t1 typ1 t2 n1,
  typ1 `notin` tt_fv_Typ t1 ->
  open_Typ_wrt_Typ_rec n1 t2 t1 = t_subst_Typ t2 typ1 (open_Typ_wrt_Typ_rec n1 (t_var_f typ1) t1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Typ_intro_rec :
forall t1 typ1 t2 n1,
  typ1 `notin` tt_fv_Typ t1 ->
  open_Typ_wrt_Typ_rec n1 t2 t1 = t_subst_Typ t2 typ1 (open_Typ_wrt_Typ_rec n1 (t_var_f typ1) t1).
Proof. Admitted.

Hint Resolve t_subst_Typ_intro_rec : lngen.
Hint Rewrite t_subst_Typ_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma e_subst_Exp_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` e_fv_Exp e1 ->
  open_Exp_wrt_Exp_rec n1 e2 e1 = e_subst_Exp e2 x1 (open_Exp_wrt_Exp_rec n1 (e_var_f x1) e1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_Exp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` e_fv_Exp e1 ->
  open_Exp_wrt_Exp_rec n1 e2 e1 = e_subst_Exp e2 x1 (open_Exp_wrt_Exp_rec n1 (e_var_f x1) e1).
Proof. Admitted.

Hint Resolve e_subst_Exp_intro_rec : lngen.
Hint Rewrite e_subst_Exp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma t_subst_Exp_intro_rec_mutual :
(forall e1 typ1 t1 n1,
  typ1 `notin` tt_fv_Exp e1 ->
  open_Exp_wrt_Typ_rec n1 t1 e1 = t_subst_Exp t1 typ1 (open_Exp_wrt_Typ_rec n1 (t_var_f typ1) e1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_Exp_intro_rec :
forall e1 typ1 t1 n1,
  typ1 `notin` tt_fv_Exp e1 ->
  open_Exp_wrt_Typ_rec n1 t1 e1 = t_subst_Exp t1 typ1 (open_Exp_wrt_Typ_rec n1 (t_var_f typ1) e1).
Proof. Admitted.

Hint Resolve t_subst_Exp_intro_rec : lngen.
Hint Rewrite t_subst_Exp_intro_rec using solve [auto] : lngen.

Lemma t_subst_Typ_intro :
forall typ1 t1 t2,
  typ1 `notin` tt_fv_Typ t1 ->
  open_Typ_wrt_Typ t1 t2 = t_subst_Typ t2 typ1 (open_Typ_wrt_Typ t1 (t_var_f typ1)).
Proof. Admitted.

Hint Resolve t_subst_Typ_intro : lngen.

Lemma e_subst_Exp_intro :
forall x1 e1 e2,
  x1 `notin` e_fv_Exp e1 ->
  open_Exp_wrt_Exp e1 e2 = e_subst_Exp e2 x1 (open_Exp_wrt_Exp e1 (e_var_f x1)).
Proof. Admitted.

Hint Resolve e_subst_Exp_intro : lngen.

Lemma t_subst_Exp_intro :
forall typ1 e1 t1,
  typ1 `notin` tt_fv_Exp e1 ->
  open_Exp_wrt_Typ e1 t1 = t_subst_Exp t1 typ1 (open_Exp_wrt_Typ e1 (t_var_f typ1)).
Proof. Admitted.

Hint Resolve t_subst_Exp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
