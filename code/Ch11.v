(*************************************************************************)
(** Sum Types in Coq. *)
(*************************************************************************)

Require Import Metatheory.

(* These two files are derived from the file systemt.ott *)
Require Import systemt_finite_ott.
Require Import systemt_finite_inf.
(* Derived via Ott tool. Read this file to see the definitions of the SystemT language *)
(* Note that some of the names from prior versions are slightly different:
    lc    -> lc_exp
    subst -> subst_exp
    fv    -> fv_exp
    open  -> open_exp_wrt_exp.
 *)

Notation "[ y ~> u ] e" := (subst_exp u y e) (at level 68).

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  constr:(A `union` B `union` C `union` D).

(*************************************************************************)
(** * Showing that the definitions are locally closed. *)
(*************************************************************************)

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
(** * Unicity. *)
(*************************************************************************)

Lemma unicity : forall G e t1, typing G e t1 -> forall t2, typing G e t2 -> t1 = t2.
Proof.
  intros G e t1 H. induction H; intros u T2; inversion T2; subst; auto.
  - eapply binds_unique; eauto.
  - f_equal.
    pick fresh x.
    apply (H0 x); eauto.
  - pose (K := IHtyping1 _ H4). clearbody K. inversion K. auto.
  - apply IHtyping1 in H4. apply IHtyping2 in H6. subst. auto.
  - apply IHtyping in H2. inversion H2. auto.
  - apply IHtyping in H2. inversion H2. auto.
  - apply IHtyping in H4. subst. auto.
  - apply IHtyping in H4. subst. auto.
  - apply IHtyping in H8. inversion H8. subst.
    pick fresh x. apply H1 with (x:=x); auto.
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
  - pick fresh x and apply typing_abs; eauto.
    rewrite_env (((x ~ t1) ++ G') ++ F ++ E).
    eapply H0; eauto. simpl_env. eauto.
  - pick fresh x and apply typing_case. auto.
    rewrite_env (((x ~ t1) ++ G') ++ F ++ E).
    apply H1; auto. simpl_env. auto.
    rewrite_env (((x ~ t2) ++ G') ++ F ++ E).
    apply H3; auto. simpl_env. auto.
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

(*************************************************************************)
(** * Substitution *)
(*************************************************************************)

Lemma typing_subst_var_case : forall E F u S T (y x : atom),
  binds x T (F ++ (y ~ S) ++ E) ->
  uniq (F ++ (y ~ S) ++ E) ->
  typing E u S ->
  typing (F ++ E) ([y ~> u] var_f x) T.
Proof.
  intros E F u S T z x H J K.
  simpl. destruct (x == z).
  - subst. apply binds_mid_eq in H. subst.
    apply typing_weakening. assumption.
    solve_uniq. assumption.
  - constructor. solve_uniq.
    eapply binds_remove_mid. apply H. assumption.
Qed.

Lemma typing_subst : forall (E F : env) e u S T (y : atom),
  typing (F ++ (y ~ S) ++ E) e T ->
  typing E u S ->
  typing (F ++ E) ([y ~> u] e) T.
Proof.
  intros E F e u S T y H.
  remember (F ++ (y ~ S) ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq J; subst; simpl; eauto.
  - apply typing_subst_var_case with (S:=S); auto.
  - pick fresh x and apply typing_rec; auto;
      apply typing_lc in J as J1;
      rewrite subst_exp_open_exp_wrt_exp_var.
    rewrite_env (((x ~ typ_nat) ++ F) ++ E).
    apply H2; auto. auto. auto.
    assert (value (open_exp_wrt_exp e1 (var_f x))); auto.
    apply value_subst; auto. auto. auto.
  - pick fresh x and apply typing_abs.
    rewrite subst_exp_open_exp_wrt_exp_var.
    rewrite_env (((x ~ t1) ++ F) ++ E).
    apply H0; auto. auto. apply typing_lc in J. auto.
  - pick fresh x and apply typing_case; auto;
      apply typing_lc in J as J1;
      rewrite subst_exp_open_exp_wrt_exp_var.
    rewrite_env (((x ~ t1) ++ F) ++ E).
    apply H1; auto. auto. auto.
    rewrite_env (((x ~ t2) ++ F) ++ E).
    apply H3; auto. auto. auto.
Qed.


Lemma typing_subst_simple : forall (E : env) e u S T (z : atom),
  typing ((z ~ S) ++ E) e T ->
  typing E u S ->
  typing E ([z ~> u] e) T.
Proof.
  intros.
  eapply typing_subst with (F := nil). eauto. eauto.
Qed.

(*************************************************************************)
(** Dynamics *)
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
    - inversion H. pick fresh x.
      rewrite (subst_exp_intro x); auto.
      eapply subst_exp_lc_exp; eauto using value_lc.
    - inversion H. pick fresh x for (fv_exp e1).
      eapply lc_rec; eauto.
    - inversion H. inversion H5. pick fresh x.
      rewrite (subst_exp_intro x); auto.
      eapply lc_fapp; eauto.
      eapply subst_exp_lc_exp; eauto using value_lc.
    - inversion H; subst. constructor; auto.
    - inversion H; subst. pick fresh x.
      rewrite (subst_exp_intro x); auto.
      eapply subst_exp_lc_exp; auto using value_lc.
    - inversion H; subst. pick fresh x.
      rewrite (subst_exp_intro x); auto.
      eapply subst_exp_lc_exp; auto using value_lc.
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
    - apply IHF. exists e'0. auto.
    - apply IHF1. exists e1'. auto.
    - apply IHF2. exists e2'. auto.
    - apply IHF. exists e'0. auto.
    - apply IHF. exists e'0. auto.
  Qed.

End Evaluation.
Export Evaluation.

Module EvaluationTS := TransitionSystemProperties Evaluation.
Export EvaluationTS.

(*************************************************************************)
(** * Preservation *)
(*************************************************************************)

Lemma preservation : forall (E : env) e e' T,
  typing E e T ->
  eval e e' ->
  typing E e' T.
Proof.
  intros E e e' T H.
  generalize dependent e'.
  induction H; intros e' J;
    inversion J; subst; auto.
  - pick fresh x and apply typing_rec.
    apply IHtyping1. auto. auto.
    apply H1. auto. apply H3. auto.
  - eapply typing_fapp.
    + pick fresh x.
      rewrite subst_exp_intro with (x1:=x).
      eapply typing_subst_simple. apply H1. auto.
      inversion H. auto. auto.
    + pick fresh x and apply typing_rec.
      inversion H. auto.
      auto. apply H1. auto. apply H3. auto.
  - eapply typing_fapp. apply IHtyping1. auto. auto.
  - eapply typing_fapp. apply H. auto.
  - inversion H; subst.
    pick fresh x. rewrite subst_exp_intro with (x1:=x).
    eapply typing_subst_simple. apply H4. auto. auto. auto.
  - eapply typing_fst. apply IHtyping. apply H1.
  - inversion H; subst; auto.
  - eapply typing_snd. apply IHtyping. apply H1.
  - inversion H; subst; auto.
  - pick fresh x and apply typing_case. apply IHtyping; auto.
    apply H0; auto. apply H2; auto.
  - pick fresh x. rewrite subst_exp_intro with (x1:=x).
    eapply typing_subst_simple. apply H0; auto.
    inversion H; auto. auto.
  - pick fresh x. rewrite subst_exp_intro with (x1:=x).
    eapply typing_subst_simple. apply H2; auto.
    inversion H; auto. auto.
Qed.

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

Lemma canonical_forms_pair : 
  forall e T1 T2, value e -> typing nil e (typ_prod T1 T2) ->
             exists e1 e2, e = pair e1 e2 /\ value e1 /\ value e2.
Proof.
  intros e T1 T2 V TH. inversion V; subst; inversion TH; subst.
  exists e1. exists e2. auto.
Qed.

(* canonical form of sums *)
Lemma canonical_forms_sum :
  forall e T1 T2, value e -> typing nil e (typ_sum T1 T2) ->
             (exists e', value e' /\ e = inl T2 e') \/
             (exists e', value e' /\ e = inr T1 e').
Proof.
  intros e T1 T2 HV. induction HV; intro HT; inversion HT; subst.
  - left. exists e. auto.
  - right. exists e. auto.
Qed.

Lemma void_has_no_value: forall e,
  value e -> ~ (typing nil e typ_void).
Proof.
  intros e HV. induction HV; intro HT; inversion HT.
Qed.

Lemma progress : forall e T,
  typing nil e T ->
  value e \/ exists e', eval e e'.
Proof.
  intros e T H.
  assert (typing nil e T); auto.
  remember nil as G.
  induction H; subst; auto.
  - inversion H1.
  - destruct IHtyping. auto. auto.
    + constructor. auto.
    + right. destruct H1. exists (s x). auto.
  - destruct IHtyping1. auto. auto.
    + apply (canonical_forms_nat _ H5) in H.
      destruct H.
      * subst. right. exists e0. constructor.
        apply typing_lc in H0. auto.
        apply typing_lc in H1. auto.
      * destruct H. destruct H. subst.
        right. eapply ex_intro. apply eval_rec_s.
        apply typing_lc in H0. auto.
        apply typing_lc in H1. auto. auto.
    + destruct H5. right.
      eapply ex_intro. apply eval_rec_scrut.
      apply typing_lc in H0. auto.
      apply typing_lc in H1. auto. eauto.
  - apply typing_lc in H0. left. constructor. auto.
  - destruct IHtyping1; auto.
    + destruct IHtyping2; auto.
      * right. 
        apply (canonical_forms_arr _ t1 t2 H2) in H.
        destruct H. subst.
        inversion H0. subst. apply typing_lc in H6.
        eapply ex_intro. apply eval_beta; auto.
      * destruct H3. right. eapply ex_intro.
        apply eval_fapp_right; eauto.
    + destruct H2. right.
      eapply ex_intro. apply eval_fapp_left.
      apply typing_lc in H1. auto. eauto.
  - destruct IHtyping1; auto.
    + destruct IHtyping2; auto.
      right. destruct H3. exists (pair e1 x).
      apply eval_pair_right; auto.
    + right. destruct H2. exists (pair x e2).
      apply eval_pair_left; eauto using typing_lc.
  - destruct IHtyping; auto.
    + apply (canonical_forms_pair _ t1 t2) in H1. right.
      destruct H1 as [e1 [e2 [p [v1 v2]]]]; subst; auto.
      eapply ex_intro. eauto. auto.
    + destruct H1. right. exists (fst x). constructor; auto.
  - destruct IHtyping; auto.
    + apply (canonical_forms_pair _ t1 t2) in H1. right.
      destruct H1 as [e1 [e2 [p [v1 v2]]]]; subst; auto.
      eapply ex_intro. eauto. auto.
    + destruct H1. right. exists (snd x). constructor; auto.
  - destruct IHtyping; auto.
    + apply void_has_no_value in H1. contradiction.
    + destruct H1. right. exists (abort t x). auto.
  - destruct IHtyping; auto.
    destruct H1. right. eapply ex_intro. eauto.
  - destruct IHtyping; auto.
    destruct H1. right. eapply ex_intro. eauto.
  - destruct IHtyping; auto.
    + apply (canonical_forms_sum _ t1 t2) in H5; auto.
      destruct H5; destruct H5; destruct H5; subst.
      * right. eapply ex_intro.
        apply eval_casel; eauto using typing_lc.
      * right. eapply ex_intro.
        apply eval_caser; eauto using typing_lc.
    + right. destruct H5. eapply ex_intro.
      apply eval_case; eauto using typing_lc.
Qed.

(*************************************************************************)
(** * Booleans *)
(*************************************************************************)

Definition typ_bool := typ_sum typ_unit typ_unit.
Definition true := inl typ_unit null.
Definition false := inr typ_unit null.
Definition bif e e1 e2 := scase e e1 e2.

Theorem true_is_bool: forall G,
    uniq G ->
    typing G true typ_bool.
Proof.
  intros G H. constructor. auto.
Qed.

Theorem false_is_bool: forall G,
    uniq G ->
    typing G false typ_bool.
Proof.
  intros G H. constructor. auto.
Qed.

Theorem bif_type_check: forall G e e1 e2 T,
    typing G e typ_bool ->
    typing G e1 T ->
    typing G e2 T ->
    typing G (bif e e1 e2) T.
Proof.
  intros G e e1 e2 T HT HT1 HT2.
  unfold bif. pick fresh x and apply typing_case.
  apply HT.
  rewrite open_exp_wrt_exp_lc_exp; eauto using typing_lc.
  apply typing_weakening; auto. eauto using typing_uniq.
  rewrite open_exp_wrt_exp_lc_exp; eauto using typing_lc.
  apply typing_weakening; auto. eauto using typing_uniq.
Qed.

(*************************************************************************)
(** * Option types *)
(*************************************************************************)

Definition typ_option t := typ_sum typ_unit t.
Definition none t := inl t null.
Definition just e := inr typ_unit e.
Definition ifnull e e1 e2 := scase e e1 e2.

Theorem none_is_option: forall G T,
    uniq G ->
    typing G (none T) (typ_option T).
Proof.
  intros G T H. constructor. auto.
Qed.

Theorem just_is_option: forall G e T,
    typing G e T ->
    typing G (just e) (typ_option T).
Proof.
  intros G e T H. constructor. auto.
Qed.

Theorem ifnull_type_check: forall L G e e1 e2 T1 T2,
    typing G e (typ_option T1) ->
    typing G e1 T2 ->
    (forall x, x \notin L -> typing ((x ~ T1) ++ G) (open_exp_wrt_exp e2 (var_f x)) T2) ->
    typing G (ifnull e e1 e2) T2.
Proof.
  intros L G e e1 e2 T1 T2 HT HT1 HT2.
  pick fresh x and apply typing_case. apply HT.
  rewrite open_exp_wrt_exp_lc_exp; eauto using typing_lc.
  apply typing_weakening; auto. eauto using typing_uniq.
  apply HT2; auto.
Qed.

(*************************************************************************)
(** * Lists *)
(*************************************************************************)

Definition lnil t := inl t null.
Definition cons e1 e2 := inr typ_unit (pair e1 e2).

(* what is the type of (cons z lnil) ? *)
Example list1:
  typing nil (cons z (lnil typ_nat)) (typ_sum typ_unit (typ_prod typ_nat (typ_sum typ_unit typ_nat))).
Proof.
  apply typing_inr. apply typing_pair. apply typing_z; auto.
  apply typing_inl. apply typing_null; auto.
Qed.

(* what is the type of (cons z (cons z nil)) ? *)

Example list2:
  typing nil (cons z (cons z (lnil typ_nat))) (typ_sum typ_unit (typ_prod typ_nat (typ_sum typ_unit (typ_prod typ_nat (typ_sum typ_unit typ_nat))))).
Proof.
  apply typing_inr. apply typing_pair. apply typing_z; auto.
  apply list1.
Qed.

(* see the pattern here? *)

Example list3:
  typing nil (cons z (cons z (cons z (lnil typ_nat)))) (typ_sum typ_unit (typ_prod typ_nat (typ_sum typ_unit (typ_prod typ_nat (typ_sum typ_unit (typ_prod typ_nat (typ_sum typ_unit typ_nat))))))).
Proof.
  apply typing_inr. apply typing_pair. apply typing_z; auto.
  apply list2.
Qed.
