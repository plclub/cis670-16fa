(* Examples of Primitive Recursion and Iteration in Coq *)

Require Import Arith.

Print nat.

(* This is the 'rec' operator from SystemT *)

Fixpoint rec (A : Type) (n : nat) : A -> (nat -> A -> A) -> A :=
  fun z s =>
    match n with
    | O => z
    | S x => s x (rec A x z s)
    end.

(* This is the 'iter' operator. Notice the difference in the 's' argument. It does 
   not get access to the predecessor x. *)

Fixpoint iter (A : Type) (n : nat) : A -> (A -> A) -> A := fun z s => 
  match n with
  | O => z
  | S x => s (iter A x z s)
  end.

(* Examples using primitive recursion *)

Definition add : nat -> nat -> nat := fun x y => rec nat x y (fun x' r => r).

Compute (add O (S (S O))).

Definition pred := fun x => rec nat x O (fun x' _ => x').

Definition sub := fun x y => rec nat y x (fun y' r => pred r).

Compute (sub 5 2).

(* Defining rec in terms of ind and proving them equivalent. *)

Definition rec' : forall A, nat -> A -> (nat -> A -> A) -> A :=
  fun A x z s => 
    snd (iter (nat * A) x (O, z) (fun xx => ( S (fst xx), s (fst xx) (snd xx)))).

Lemma helper : forall A n z s,
    n = fst (iter (nat * A) n (0, z) (fun xx : nat * A => (S (fst xx), s (fst xx) (snd xx)))).
Proof.
  intros. induction n.
  - simpl. auto.
  - simpl. rewrite <- IHn. auto.
Qed.
    
Lemma same : forall A n z s, rec A n z s = rec' A n z s.
Proof.
  intros A n. induction n.
  - intros. unfold rec'. simpl. auto.
  - intros. unfold rec'. simpl.
    unfold rec' in IHn. rewrite IHn.
    f_equal. rewrite <- helper. auto.
Qed.

(* Mutual recursion *)

Definition eo : nat -> nat * nat :=
  fun n => iter (nat * nat) n (S O, O) (fun b => (snd b, fst b)).

Definition even := fun x => fst (eo x).
Definition odd  := fun x => snd (eo x).

Compute (odd 2).
Compute (even 2).

