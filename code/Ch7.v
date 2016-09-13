Require Export Metalib.Metatheory.
Require Export Transitions.
Require Export Ch6.

(* Chapter 7: The Evaluation dynamics relation presented in this chapter is more commonly called
   a "bigstep" semantics" *)



(*************************************************************************)
(** * Structural Dynamics 7.1 *)
(*************************************************************************)

(* We can define the inductive relation shown in 7.1 as below *)
Inductive bigstep : exp -> exp -> Prop :=
| big_num : forall i, bigstep (exp_num i) (exp_num i)
                         
| big_str : forall i, bigstep (exp_str i) (exp_str i)
                         
| big_plus : forall e1 i1 e2 i2,
    bigstep e1 (exp_num i1) ->
    bigstep e2 (exp_num i2) ->
    bigstep (exp_op plus e1 e2) (exp_num (i1 + i2))
            
| big_let : forall e1 v1 e2 v2,
    bigstep e1 v1 ->
    bigstep (open e2 v1) v2 ->
    bigstep (exp_let e1 e2) v2.

Hint Constructors bigstep.

(* Lemma 7.1 *)
Lemma bigstep_value : forall e v, bigstep e v -> value v.
Proof.
  intros e v B. induction B; auto.
Qed.

(* Our representation requires this as well. *)
Lemma bigstep_lc_1 : forall e1 e2, bigstep e1 e2 -> lc e1.
Proof.
  intros e1 e2 B. induction B; auto.
  pick fresh x and apply lc_let; auto.
  rewrite (subst_intro x) in IHB2; auto.
  apply (subst_lc_inverse x v1) in IHB2.
  auto. destruct (bigstep_value e1 v1 B1); auto.
Qed.  

(*************************************************************************)
(** * Relating Structural and Evaluation Dynamics 7.2 *)
(*************************************************************************)

Lemma big_to_small : forall e v, bigstep e v -> multistep e v.
Proof.
Admitted.  (* needs congruence lemma from Ch5.v, as well as multistep_transitive *)

Lemma small_to_big : forall e e', step e e' -> forall v, bigstep e' v -> bigstep e v.
Proof.
Admitted.
