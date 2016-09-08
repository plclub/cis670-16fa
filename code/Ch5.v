Require Export Metalib.Metatheory.
Require Export Ch4.

(*************************************************************************)
(** * Transition Systems *)
(*************************************************************************)

(* The beginning of Ch5 introduces general terminology for reasoning about 
   the evaluation of programs.  We can capture the generality of these 
   definition using Coq's module system. The following module type 
   defines what it means to be a transition system in abstract terms. 
 *)

Module Type TransitionSystem.
  Parameter S : Set.
  Parameter state : S -> Prop.

  Parameter final : S -> Prop.
  Axiom final_state : forall s, final s -> state s.

  Parameter initial : S -> Prop.
  Axiom initial_state : forall s, initial s -> state s.
  
  Parameter step : S -> S -> Prop.
  Axiom step_states : forall s1 s2, step s1 s2 -> state s1 /\ state s2.

  Axiom final_does_not_step : forall s, final s -> not (exists s', step s s').    
  
End TransitionSystem.

(* Once we know what a transition system is, we can define concepts 
   and prove theorems in terms of the basic definitions above. *)

Module TransitionSystemProperties (TS : TransitionSystem).
  Import TS.

  Definition stuck (s : S) :=
    not (final s) /\ not (exists s', step s s').
                         
  Fixpoint transitions (ss : list S) (last : S -> Prop) : Prop := 
    match ss with
    | nil => False
    | si :: rest => match rest with
                     | nil => last si
                     | si' :: _ => step si si' /\ transitions rest last
                   end
    end.

  Definition transition_sequence ss : Prop :=
    match ss with
    | s0 :: _ => initial s0 /\ transitions ss (fun _ => True)
    | _ => False
    end.

  Definition maximal_transition_sequence ss : Prop :=
    match ss with
    | s0 :: _ => initial s0 /\ transitions ss (fun sn => not (exists s', step sn s'))
    | _ => False
    end.

  Definition complete_transition_sequence ss : Prop :=
    match ss with
    | s0 :: _ => initial s0 /\ transitions ss final
    | _ => False
    end.
  
  Inductive multistep : S -> S -> Prop :=
    | multistep_refl : forall s,  multistep s s
    | multistep_step : forall s s' s'', step s s' -> multistep s' s'' -> multistep s s''.        

  Hint Constructors multistep.
  Lemma multistep_transitive : forall s s' s'',
      multistep s s' -> multistep s' s'' -> multistep s s''.
  Proof.
    intros s s' s'' MS1 MS2.
    induction MS1.
    - auto.
    - eauto. 
  Qed.

End TransitionSystemProperties.  

(*************************************************************************)
(** * Values and Evaluation (i.e. Structural Dynamics)                   *)
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
Import Evaluation.

(* Because our Evaluation Module is a Transition System, we can make the general 
   definitions from the TransitionSystemProperties module available to us. *)

Module EvaluationTS := TransitionSystemProperties Evaluation.
Import EvaluationTS.

Lemma finality_of_values : forall e, lc e -> not (value e /\ exists e', eval e e').
Proof.
  intros e LC. induction LC; unfold not; intro K; destruct K as [VK [e' EV]].
  - inversion VK.
  - inversion EV.
  - inversion EV.
  - inversion VK.
  - inversion VK.
Qed.

(** *** Exercise: Prove Lemma 5.3 *)
Lemma determinacy : forall e e1, eval e e1 -> forall e2, eval e e2 -> e1 = e2.
Proof.
(* Fill in HERE *) Admitted.

Lemma multistep_determinacy : forall e e1, multistep e e1, forall e2, multistep e e2 -> e1 = e2.

(*************************************************************************)
(** * Optional 5.3 Contextual Dynamics *)
(*************************************************************************)

(*************************************************************************)
(** * Optional: 5.4 Equational Dynamics *)
(*************************************************************************)


