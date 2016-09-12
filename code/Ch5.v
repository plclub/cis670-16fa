Require Export Metalib.Metatheory.
Require Export Ch4.
Require Export Transitions. 

(*************************************************************************)
(** * Values and Evaluation (i.e. Structural Dynamics 5.2)               *)
(*************************************************************************)

(** In order to state the preservation lemma, we first need to define
    values and the small-step evaluation relation.  These inductive
    relations are straightforward to define.
    Note the hypotheses which ensure that the relations hold only for
    locally closed terms.  Below, we prove that this is actually the
    case, since it is not completely obvious from the definitions
    alone.
*)

Inductive value : exp -> Prop :=
| value_num : forall i,
    value (exp_num i)
| value_str : forall s,
    value (exp_str s).

Inductive eval : exp -> exp -> Prop :=
| eval_op_plus : forall n1 n2,
    eval (exp_op plus (exp_num n1) (exp_num n2)) (exp_num (n1 + n2))
| eval_op_fst : forall e1 e1' e2 op,
    eval e1 e1' ->
    lc e2 ->
    eval (exp_op op e1 e2) (exp_op op e1' e2)
| eval_op_snd : forall e1 e2 e2' op,
    value e1 -> eval e2 e2' ->
    eval (exp_op op e1 e2) (exp_op op e1 e2')
| eval_let_rhs : forall e1 e1' e2,
    eval e1 e1' ->
    lc (exp_let e1 e2) ->
    eval (exp_let e1 e2) (exp_let e1' e2)
| eval_let_red : forall e1 e2,
    value e1 ->
    lc (exp_let e1 e2) ->
    eval (exp_let e1 e2) (open e2 e1).

(** We add the constructors for these two relations as hints to be used
    by Coq's [auto] and [eauto] tactics.
*)

Hint Constructors value eval.

Module Evaluation.
  Definition S := exp.
  Definition state := lc.
  Definition initial := lc.
  Definition final := value.
  Definition step  := eval.
  Lemma final_state : forall e, value e -> lc e.
  Proof. 
    intros e H. inversion H. auto. auto.
  Qed.
  Lemma initial_state : forall e, initial e -> lc e.
  Proof.
    intros. auto.
  Qed.
  Lemma step_states : forall (e1:exp) (e2:exp), eval e1 e2 -> lc e1 /\ lc e2.
  Proof.
    intros e1 e2 H. induction H.
    - auto.
    - destruct IHeval. auto.
    - destruct IHeval. auto using final_state.
    - destruct IHeval. inversion H0. eauto.
    - inversion H0. split. eauto using final_state.
      pick fresh x.
      rewrite (subst_intro x).
      apply subst_lc. auto. auto. auto.
  Qed.    

  Lemma final_does_not_step : forall (e:exp), final e -> not (exists e', step e e').
  Proof.
    intros e F. unfold not. intros H. inversion F;
    subst; destruct H as [e' S]; inversion S.
  Qed.

End Evaluation.
Export Evaluation.

(* Here is a analogous version of 'final does not step' *)
Lemma finality_of_values : forall e, lc e -> not (value e /\ exists e', eval e e').
Proof.
  intros e LC. induction LC; unfold not; intro K; destruct K as [VK [e' EV]].
  - inversion VK.
  - inversion EV.
  - inversion EV.
  - inversion VK.
  - inversion VK.
Qed.

(* Because our Evaluation Module is a Transition System, we can make the general 
   definitions from the TransitionSystemProperties module available to us. *)

Module EvaluationTS := TransitionSystemProperties Evaluation.
Export EvaluationTS.


(* Some of our eval rules are called *congruence* rules. These rules exist to find the 
   actual action in term for the reduction. 
   We can lift each of the congruence rules through the multistep relation. 
   For example, if we have a sequence of steps, we can lift that to an evaluation in 
   the righthand side of a let expression.
*)

Lemma multistep_let_rhs : forall e1 e1' e2,
    multistep e1 e1' -> state (exp_let e1 e2) -> multistep (exp_let e1 e2) (exp_let e1' e2).
Proof.
  intros e1 e1' e2 MS. induction MS; intros S; inversion S.
  - eapply ms_refl. eapply lc_let; auto. 
  - eapply ms_step; eauto. eapply eval_let_rhs; eauto.
    eapply IHMS; eapply lc_let; eauto.
    eapply step_states. eauto.
Qed.   

(** *** Exercise: State and prove congruence lemmas for eval_op_fst and 
    eval_op snd.  *)

(** *** Exercise: Prove Lemma 5.3 *)
Lemma determinacy : forall e e1, eval e e1 -> forall e2, eval e e2 -> e1 = e2.
Proof.
(* Fill in HERE *) Admitted.


(*************************************************************************)
(** * Optional 5.3 Contextual Dynamics *)
(*************************************************************************)

(*************************************************************************)
(** * Optional: 5.4 Equational Dynamics *)
(*************************************************************************)

(** *** Challenge exercise: Define the "definitional equality relation" as presented 
    in the textbook and Prove Theorem 5.5 *)

Inductive defeq : env -> exp -> exp -> typ -> Prop :=
  (* Finish me *)
.

(* Your definition of defeq above should validate this property. If you can't prove 
   it straightaway, you may need to add additional preconditions to your rules. *)
Lemma defeq_typing : forall G e1 e2 t, defeq G e1 e2 t -> typing G e1 t /\ typing G e2 t.
Admitted.


(* This is the "straighforward" direction mentioned in the book.  You shouldn't try
   to prove it directly. Instead, think about some simpler properties that you can 
   show first to relate step and defeq. *)
Lemma eval_defeq : forall G e e' t e0,
    typing G e t -> typing G e' t -> multistep e e0 -> multistep e' e0 -> defeq G e e' t.
Admitted.

(* This is the converse, which requires a more general property to be shown first.  *)
Lemma defeq_eval : forall G e e' t, defeq G e e' t -> exists e0, value e0 /\ multistep e e0 /\ multistep e' e0.
Admitted.



    