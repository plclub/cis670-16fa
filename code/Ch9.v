
(*************************************************************************)
(** System T in Coq. *)
(*************************************************************************)

Require Import Metatheory.

(* These two files are derived from the file systemt.ott *)
Require Import systemt_ott.
(* Derived via Ott tool. Read this file to see the definitions of the SystemT language *)
(* Note that some of the names from prior versions are slightly different:
    lc    -> lc_exp
    subst -> subst_exp
    fv    -> fv_exp
    open  -> open_exp_wrt_exp.
 *)

Notation "[ y ~> u ] e" := (subst_exp u y e) (at level 68).

Require Import systemt_inf.
(* Derived via LNgen tool. Do NOT read this file :-). Note that it includes 
   many properties about the syntax of SystemT that we proved by hand before, 
   as well as MANY other properties.
 *)


SearchAbout subst_exp.

Check subst_exp_lc_exp.   (* similar to subst_lc from before *)
Check subst_exp_intro.    (* similar to subst_intro from before *)

(* Below, we reprove many of the facts about the E language for 
   SystemT *)


(*************************************************************************)
(** * Showing that the definitions are locally closed. *)
(*************************************************************************)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  constr:(A `union` B `union` C `union` D).

Lemma typing_lc : forall G e T, typing G e T -> lc_exp e.
Proof. 
  intros. induction H; eauto.
Qed.

Lemma typing_uniq : forall G e T, typing G e T -> uniq G.
Proof.
  intros. induction H; eauto.
  - pick fresh x for L.
    pose (K := H0 x Fr). clearbody K. inversion K. auto.
Qed.




(*************************************************************************)
(** * Unicity of Typing *)
(*************************************************************************)

Lemma unicity : forall G e t1, typing G e t1 -> forall t2, typing G e t2 -> t1 = t2.
Proof.
  intros G e t1 H. induction H; intros u T2; inversion T2; subst; auto.
  - eapply binds_unique; eauto.
  - f_equal.
    pick fresh x.
    apply (H0 x); eauto.
  - pose (K := IHtyping1 _ H4). clearbody K. inversion K. auto.
Qed.    

(*************************************************************************)
(** * Weakening *)
(*************************************************************************)

Lemma typing_weakening_strengthened :  forall E F G e T,
  typing (G ++ E) e T ->
  uniq (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof.
  intros E F G e T H.
  remember (G ++ E) as E'.
  generalize dependent G.
  induction H; intros G' Eq Uniq; subst; eauto.
  - pick fresh x and apply typing_rec; eauto.
    rewrite_env (((x ~ typ_nat) ++ G') ++ F ++ E).
    eapply H2; eauto. simpl_env. eauto.
  - pick fresh x and  apply typing_abs; eauto.
    rewrite_env (((x ~ t1) ++ G') ++ F ++ E).
    eapply H0; eauto. simpl_env. eauto.
Qed.    

Lemma typing_weakening : forall E F e T,
    typing E e T ->
    uniq (F ++ E) ->
    typing (F ++ E) e T.
Proof.
  intros E F e T H J.
  rewrite_env (nil ++ F ++ E).
  apply typing_weakening_strengthened; auto.
Qed.

(*************************************************************************)
(** * Substitution *)
(*************************************************************************)


Lemma value_subst : forall x v u,
    lc_exp v ->
    value u ->
    value ([x ~> v]u).
Proof.
  intros x v u Lc Hu.
  induction Hu; subst; simpl; auto.
  apply val_abs.
  apply subst_exp_lc_exp with (e1 := abs t e). eauto.
  eauto.
Qed.

Lemma typing_subst_var_case : forall E F u S T (y x : atom),
  binds x T (F ++ (y ~ S) ++ E) ->
  uniq (F ++ (y ~ S) ++ E) ->
  typing E u S ->
  typing (F ++ E) ([y ~> u] var_f x) T.
Proof.
  intros E F u S T z x H J K.
  simpl.
 (* EXERCISE *) Admitted.

Lemma typing_subst : forall (E F : env) e u S T (y : atom),
  typing (F ++ (y ~ S) ++ E) e T ->
  typing E u S ->
  typing (F ++ E) ([y ~> u] e) T.
Proof.
  intros. remember (F ++ (y ~ S) ++ E) as G.
  generalize dependent F.
  induction H; intros; subst; 
    eauto using typing_uniq, typing_subst_var_case;
    simpl; eauto using typing_weakening.
  - pick fresh x and apply typing_rec; eauto.
    rewrite_env (((x~ typ_nat) ++ F) ++ E).
    admit.
    
(* EXERCISE *) Admitted.

Lemma typing_subst_simple : forall (E : env) e u S T (z : atom),
  typing ((z ~ S) ++ E) e T ->
  typing E u S ->
  typing E ([z ~> u] e) T.
Proof.
  intros.
  eapply typing_subst with (F := nil). eauto. eauto.
Qed.


(*************************************************************************)
(** * Renaming *)
(*************************************************************************)

Lemma typing_rename : forall (x y : atom) E e T1 T2,
  x `notin` fv_exp e -> y `notin` (dom E `union` fv_exp e) ->
  typing ((x ~ T1) ++ E) (open_exp_wrt_exp e (var_f x)) T2 ->
  typing ((y ~ T1) ++ E) (open_exp_wrt_exp e (var_f y)) T2.
Proof.
  intros x y E e T1 T2 Fr1 Fr2 H.
  destruct (x == y).
  - Case "x = y".
    subst; eauto.
  - Case "x <> y".
    assert (J : uniq ((x ~ T1) ++ E)).
      eapply typing_uniq; eauto.
    assert (J' : uniq E).
      inversion J; eauto.
    rewrite (@subst_exp_intro x); eauto.
    rewrite_env (nil ++ (y ~ T1) ++ E).
    apply typing_subst with (S := T1).
    simpl_env.
    + SCase "(open x s) is well-typed".
      apply typing_weakening_strengthened. eauto. auto.
    + SCase "y is well-typed".
      eapply typing_var; eauto.
Qed.

  
Lemma value_rename : forall (x y : atom) e,
  x `notin` fv_exp e ->
  value (open_exp_wrt_exp e (var_f x)) ->
  value (open_exp_wrt_exp e (var_f y)).
Proof.
  intros x y e Fr V.
  destruct (x == y). subst. auto.
  rewrite (@subst_exp_intro x); eauto.
  apply value_subst; eauto.
Qed.
  
(*************************************************************************)
(** * Exists-Fresh Definitions *)
(*************************************************************************)
 
Lemma typing_rec_exists : forall x (E : env) (e e1 e2 : exp) (T : typ),
    typing E e typ_nat
    -> typing E e1 T
    -> x `notin` fv_exp e2
    -> value (open_exp_wrt_exp e2 (var_f x))
    -> typing ((x ~ typ_nat) ++ E) (open_exp_wrt_exp e2 (var_f x)) (typ_arr T T) 
    -> typing E (rec e e1 e2) T.
Proof.
  intros x E e e1 e2 T T2 Te1 Fr V2 Te2.
  pick fresh y and apply typing_rec; eauto.
  - apply typing_rename with (x := x); auto.
  - apply value_rename with (x:= x); auto.
Qed.

Lemma typing_abs_exists : forall x (E : env) (e1 : exp) (T1 T2 : typ),
      x `notin` fv_exp e1
    -> typing ((x ~ T1) ++ E) (open_exp_wrt_exp e1 (var_f x)) T2 
    -> typing E (abs T1 e1) (typ_arr T1 T2).
Proof.
  intros x E e1 T1 T2 H H0.
  pick fresh y and apply typing_abs; eauto.
  - apply typing_rename with (x := x); auto.
Qed.


(*************************************************************************)
(** Dynamics (section 9.2) *)
(*************************************************************************)

Require Import Transitions.

Module Evaluation.
  Definition S := exp.
  Definition state := lc_exp.
  Definition initial := lc_exp.
  Definition final := value.
  Definition step  := eval.
  
  Lemma value_lc : forall e, value e -> lc_exp e.
  Proof. 
    intros e H. induction H; auto.
  Qed.
  Lemma initial_state : forall e, initial e -> state e.
  Proof.
    intros. auto.
  Qed.

  Definition final_state := value_lc.
  
  Lemma eval_lc1 : forall e1 e2, eval e1 e2 -> lc_exp e1.
  Proof.
    intros e1 e2 H. induction H; auto using value_lc.
  Qed.

  Lemma eval_lc2 : forall e1 e2, eval e1 e2 -> lc_exp e2.
  Proof.
    intros e1 e2 H. induction H; eauto using value_lc.
    - inversion H. pick fresh x for (fv_exp e1).
      rewrite (subst_exp_intro x); auto.
      eapply subst_exp_lc_exp; eauto using value_lc.
    - inversion H. pick fresh x for (fv_exp e1).
      eapply lc_rec; eauto.
    - inversion H. inversion H5. pick fresh x for (fv_exp e1).
      rewrite (subst_exp_intro x); auto.
      eapply lc_app; eauto.
      eapply subst_exp_lc_exp; eauto using value_lc.
  Qed.
  
  Lemma step_states : forall (e1:exp) (e2:exp), eval e1 e2 -> state e1 /\ state e2.
  Proof.
    intros e1 e2 H. split. eapply eval_lc1; eauto. eapply eval_lc2; eauto.
  Qed.

  Lemma final_does_not_step : forall (e:exp), final e -> not (exists e', step e e').
  Proof.
    intros e F. unfold not.
    induction F; intros N;
      destruct N as [e' S]; inversion S.
    apply IHF. exists e'0. auto.
  Qed.

End Evaluation.
Export Evaluation.

Module EvaluationTS := TransitionSystemProperties Evaluation.
Export EvaluationTS.

(*************************************************************************)
(** * Preservation *)
(*************************************************************************)

(** *** Exercise [preservation for System T] *)
Lemma preservation : forall (E : env) e e' T,
  typing E e T ->
  eval e e' ->
  typing E e' T.
Proof.
Admitted.

(*************************************************************************)
(** * Progress *)
(*************************************************************************)

Lemma canonical_forms_nat :
  forall e, value e -> typing nil e typ_nat ->
       e = z \/ exists e', e = s e' /\ value e'.
Proof.
  intros e V. induction V; intros TH; inversion TH; auto.
  right. exists e. auto.
Qed.

Lemma canonical_forms_arr :
  forall e T1 T2, value e -> typing nil e (typ_arr T1 T2) ->
             exists e', e = abs T1 e'.
Proof.
  intros e T1 T2 V TH. inversion V; subst; inversion TH; auto.
  exists e0. auto.
Qed.

(** *** Exercise [Progress for System T] *)
Lemma progress : forall e T,
  typing nil e T ->
  value e \/ exists e', eval e e'.
Proof.
Admitted.

(*************************************************************************)
(** * Ackerman's function (Section 9.3) *)
(*************************************************************************)

(* Let's see how to define various example terms from Section 9.3 in this 
   calculus. *)

(* First the identity function. *)
Definition id : exp := abs typ_nat (var_b 0).

(* We can show that it type checks *)
Lemma typing_id : typing nil id (typ_arr typ_nat typ_nat).
Proof.
  (* This tactic instructs Coq to unfold the definition above. *)
  unfold id.
  (* Here we can see by the form of the term that we should use typing_abs. *)
  pick fresh x and apply typing_abs.
  (* To make more progress, we need to reduce the "opening" of the term. *)
  unfold open_exp_wrt_exp. simpl.
  (* Now we can typecheck the variable. *)
  apply typing_var.
  + auto.  (* via metatheory library *)
  + auto.  (* via metatheory library *)
Qed.

(** *** EXERCISE [comp]. Replace z below with the correct definition of comp 
    and show that it typechecks. *)

Definition comp : exp := z. (* replace with correct definition *)

Lemma typing_comp : typing nil comp (typ_arr
                                      (typ_arr typ_nat typ_nat)
                                      (typ_arr
                                         (typ_arr typ_nat typ_nat)
                                         (typ_arr typ_nat typ_nat))).
Proof.
Admitted.

(* Here is a more involved example that uses both id and comp. *)
Definition iter :=
  abs (typ_arr typ_nat typ_nat)
      (abs typ_nat
           (rec (var_b 0) id
                (abs (typ_arr typ_nat typ_nat)
                     (app (app comp (var_b 3)) (var_b 0))))).

Lemma typing_iter :
  typing nil iter (typ_arr  (typ_arr typ_nat typ_nat)
                            (typ_arr typ_nat
                                     (typ_arr typ_nat typ_nat))).
Proof.
  unfold iter.
  pick fresh f and apply typing_abs.
  unfold open_exp_wrt_exp; simpl.
  pick fresh n and apply typing_abs.
  unfold open_exp_wrt_exp; simpl.
  (* At this point, we're going to do some 'forward proving' so that we 
     don't have to prove the same thing twice. We will prove a property about 
     the argument to rec before applying the typing rule. *)
  pick fresh y.
  assert
    (typing ((y ~ typ_nat) ++ (n ~ typ_nat) ++ (f ~ typ_arr typ_nat typ_nat))
     (open_exp_wrt_exp
        (abs (typ_arr typ_nat typ_nat) (app (app comp (var_f f)) (var_b 0)))
        (var_f y)) (typ_arr (typ_arr typ_nat typ_nat) (typ_arr typ_nat typ_nat))).
  { unfold open_exp_wrt_exp; simpl.
    pick fresh g and apply typing_abs; simpl; auto.
    unfold open_exp_wrt_exp; simpl.
    (* The argument to the application is a variable in each case, so we will 
       dispatch that premise too. *)
    eapply typing_app; [|apply typing_var; auto].
    eapply typing_app; [|apply typing_var; auto].
    (* At this point, the body of the term is 'comp' above. We see this 
       with the 'fold' tactic. *)
    fold comp.
    (* We can use the lemma above to typecheck this term, but first we have 
       to use the weakening lemma. And to do that, we must put the environment 
       in the right form. *)
    rewrite_env (((g ~ typ_arr typ_nat typ_nat)
                   ++ (y ~ typ_nat)
                   ++ (n ~ typ_nat)
                   ++ (f ~ typ_arr typ_nat typ_nat)) ++ nil).
    apply typing_weakening.
    apply typing_comp. auto. }
  (* As we've already introduced the variable bound by rec (i.e. y), we'll 
     use the "exists" version of the typing rule. *)
  apply typing_rec_exists with (x:=y); simpl; eauto.
  + (* again we must use weakening to typecheck id. *)
    fold id.
    rewrite_env (((n ~ typ_nat) ++ (f ~ typ_arr typ_nat typ_nat)) ++ nil).
    eapply typing_weakening.
    apply typing_id. auto.
  + apply typing_lc in H.
    unfold open_exp_wrt_exp in *; simpl in *.
    apply val_abs. auto.
Qed.    


(** *** Challenge EXERCISE [ackerman]. Replace z below with the correct definition of comp 
    and show that it typechecks. *)

Definition ackerman := z.

Lemma typing_ackerman :
  typing nil ackerman (typ_arr typ_nat (typ_arr typ_nat typ_nat)).
Proof.
Admitted.
