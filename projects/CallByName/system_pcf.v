Require Import Metatheory.

Definition sym := atom.

Inductive typ : Set :=
| typ_nat
| typ_parr : typ -> typ -> typ.

Inductive exp : Set :=
| exp_blackhole : exp
| exp_sym  : atom -> exp
| exp_fvar : atom -> exp
| exp_bvar : nat -> exp
| exp_zero : exp
| exp_succ : exp -> exp
(* number -> zero branch -> non-zero branch -> exp *)
| exp_ifz  : exp -> exp -> exp -> exp
| exp_abs  : typ -> exp -> exp
| exp_app  : exp -> exp -> exp
| exp_fix  : typ -> exp -> exp.

Ltac solve_neq_contra :=
  match goal with
    H : ?a <> ?a
    |- _ => destruct H; reflexivity
  end.

Fixpoint fv (term : exp) : atoms :=
  match term with
  | exp_blackhole => empty
  | exp_sym  _ => empty
  | exp_fvar x => singleton x
  | exp_bvar _ => empty
  | exp_zero => empty
  | exp_succ e => fv e
  | exp_ifz num z_branch s_branch => fv num `union` fv z_branch `union` fv s_branch
  | exp_abs _ e => fv e
  | exp_app e1 e2 => fv e1 `union` fv e2
  | exp_fix _ e => fv e
  end.

Fixpoint subst (term : exp) (z : atom) (u : exp) : exp :=
  match term with
  | exp_blackhole => term
  | exp_sym  _ => term
  | exp_bvar _ => term
  | exp_fvar x => if x == z then u else term
  | exp_zero => term
  | exp_succ e => exp_succ (subst e z u)
  | exp_ifz num z_branch s_branch => exp_ifz (subst num z u)
                                            (subst z_branch z u)
                                            (subst s_branch z u)
  | exp_abs t exp => exp_abs t (subst exp z u)
  | exp_app e1 e2 => exp_app (subst e1 z u)
                            (subst e2 z u)
  | exp_fix t exp => exp_fix t (subst exp z u)
  end.

Fixpoint opening (term : exp) (x : exp) (k : nat) : exp :=
  match term with
  | exp_blackhole => term
  | exp_sym  _ => term
  | exp_fvar _ => term
  | exp_bvar k' => if k == k' then x else term
  | exp_zero => term
  | exp_succ exp => exp_succ (opening exp x k)
  | exp_ifz num z_branch s_branch => exp_ifz (opening num x k)
                                            (opening z_branch x k)
                                            (opening s_branch x (S k))
  | exp_abs t body => exp_abs t (opening body x (S k))
  | exp_app e1 e2 => exp_app (opening e1 x k) (opening e2 x k)
  | exp_fix t body => exp_fix t (opening body x (S k))
  end.

Definition open term x := opening term x 0.

Hint Unfold open.

Notation "{ k ~> u } t" := (opening t u k) (at level 67).
Notation "[ z ~> u ] e" := (subst e z u) (at level 68).

  
Ltac gather_atoms ::=
     let A := gather_atoms_with (fun x : atoms => x) in
     let B := gather_atoms_with (fun x : atom => singleton x) in
     let C := gather_atoms_with (fun x : list (atom * typ) => dom x) in
     let D := gather_atoms_with (fun x : exp => fv x) in
     let E := gather_atoms_with (fun x : list (atom * exp) => dom x) in
     constr:(A `union` B `union` C `union` D `union` E).


Lemma union_subset :
  forall s1 s2 s1' s2',
    s1 [<=] s1' -> s2 [<=] s2' -> (s1 \u s2) [<=] (s1' \u s2').
Proof.
  intros.
  Search "[<=]".
  apply KeySetProperties.union_subset_3; fsetdec.
Qed.

Lemma open_var_fv : forall e x,
    fv ({0 ~> exp_fvar x} e) [<=] fv e \u (singleton x).
Proof.
  intros e x.
  generalize dependent 0.
  induction e; intros; simpl in *; try fsetdec.
  - destruct (n0 == n).
    + simpl. fsetdec.
    + simpl. fsetdec.
  - apply IHe.
  - apply KeySetProperties.union_subset_3.
    assert (fv ({n ~> exp_fvar x} e1) [<=] union (fv e1) (singleton x)). {
      apply IHe1.
    }
    fsetdec.
    apply KeySetProperties.union_subset_3.
    assert (fv ({n ~> exp_fvar x} e2) [<=] union (fv e2) (singleton x)). {
      apply IHe2.
    }
    fsetdec.
    assert (fv ({S n ~> exp_fvar x} e3) [<=] union (fv e3) (singleton x)). {
      apply IHe3.
    }
    fsetdec.
  - assert (fv ({S n ~> exp_fvar x} e) [<=] union (fv e) (singleton x)). {
      apply IHe.
    }
    fsetdec.
  - apply KeySetProperties.union_subset_3.
    assert (fv ({n ~> exp_fvar x} e1) [<=] union (fv e1) (singleton x)). {
      apply IHe1.
    }
    fsetdec.
    assert (fv ({n ~> exp_fvar x} e2) [<=] union (fv e2) (singleton x)). {
      apply IHe2.
    }
    fsetdec.
  - assert (fv ({S n ~> exp_fvar x} e) [<=] union (fv e) (singleton x)). {
      apply IHe.
    }
    fsetdec.
Qed.
    
Lemma open_lc_core : forall e j v i u,
    i <> j
    -> {j ~> v} e = {i ~> u}({j ~> v} e)
    -> e = {i ~> u} e.
Proof.
  induction e; intros j v i u Hneq Hopen; simpl in *; try reflexivity.
  - Case "exp_bvar".
    destruct (i == n); destruct (j == n).
    + SCase "i <> j, j = i = n".
      rewrite e0 in Hneq. rewrite e in Hneq.
      solve_neq_contra.
    + SCase "i <> j, i = n, j <> n".
      subst.
      simpl in Hopen.
      destruct (n == n).
      * auto.
      * solve_neq_contra.
    + auto.
    + auto.
  - f_equal.
    eapply IHe; eauto.
    inversion Hopen.
    eassumption.
  - inversion Hopen; subst.
    f_equal.
    + eapply IHe1; eauto.
    + eapply IHe2; eauto.
    + assert (S i <> S j). {
        intros contra.
        inversion contra.
        subst.
        solve_neq_contra.
      }
      eapply IHe3; eauto.
  - inversion Hopen; subst.
    f_equal.
    assert (S i <> S j). {
      intros contra.
      inversion contra.
      subst.
      solve_neq_contra.
    }
    eapply IHe; eauto.
  - inversion Hopen; subst.
    f_equal.
    + eapply IHe1; eauto.
    + eapply IHe2; eauto.
  - inversion Hopen; subst.
    f_equal.
    assert (S i <> S j). {
      intros contra.
      inversion contra.
      subst.
      solve_neq_contra.
    }
    eapply IHe; eauto.
Qed.

Definition cost_annotated_relation (X : Type) := X -> X -> nat -> Prop.

Inductive multi {X : Type} (R : cost_annotated_relation X)
  : cost_annotated_relation X :=
| multi_refl : forall (x : X), multi R x x 0
| multi_step : forall (x y z : X) (k_xy k_yz : nat),
    R x y k_xy -> multi R y z k_yz -> multi R x z (k_xy + k_yz).

Module CallByValue.

Inductive lc : exp -> Prop :=
| lc_fvar : forall x, lc (exp_fvar x)
| lc_zero : lc exp_zero
| lc_succ : forall e, lc e -> lc (exp_succ e)
| lc_ifz : forall (L : atoms) (num z_branch s_branch : exp),
    lc num
    -> lc z_branch
    -> (forall x, x `notin` L -> lc (open s_branch (exp_fvar x)))
    -> lc (exp_ifz num z_branch s_branch)
| lc_abs : forall (L : atoms) t exp,
    (forall x, x `notin` L -> lc (open exp (exp_fvar x)))
    -> lc (exp_abs t exp)
| lc_app : forall e1 e2, lc e1
                    -> lc e2
                    -> lc (exp_app e1 e2)
| lc_fix : forall (L : atoms) t exp,
    (forall x, x `notin` L -> lc (open exp (exp_fvar x)))
    -> lc (exp_fix t exp).


Ltac solve_open_lc_main :=
  match goal with
    H : forall x : atom,
        x `notin` ?L
        -> forall k, open ?exp (exp_fvar x) = {k ~> ?u} open ?exp (exp_fvar x)
               |- _ => unfold open in H;
                     pick fresh x;
                     apply open_lc_core with (j := 0) (v := exp_fvar x);
                     try (apply H);
                     auto
end.

Lemma open_lc : forall k u e,
    lc e -> e = {k ~> u} e.
Proof.
  intros k u e Hlc.
  generalize dependent k.
  induction Hlc; try (simpl; reflexivity).
  - intros k.
    simpl.
    rewrite <- IHHlc.
    reflexivity.
  - intros k.
    simpl.
    rewrite <- IHHlc1.
    rewrite <- IHHlc2.
    f_equal.
    solve_open_lc_main.
  - intros k.
    simpl.
    f_equal.
    solve_open_lc_main.
  - intros k.
    simpl.
    rewrite <- IHHlc1.
    rewrite <- IHHlc2.
    reflexivity.
  - intros k.
    simpl.
    f_equal.
    solve_open_lc_main.
Qed.

Lemma subst_intro : forall x e u,
    x `notin` fv e
    -> {0 ~> u} e = [x ~> u] {0 ~> (exp_fvar x)} e.
Proof.
  intros x e u Hnotin.
  generalize dependent 0.
  induction e; try (simpl; reflexivity).
  - intros n.
    simpl.
    destruct (a == x).
    + rewrite e in Hnotin. simpl in Hnotin.
      fsetdec.
    + reflexivity.
  - intros n0.
    simpl in *.
    destruct (n0 == n).
    + simpl.
      destruct (x == x).
      * reflexivity.
      * solve_neq_contra.
    + simpl.
      reflexivity.
  - intros n.
    simpl in *.
    f_equal.
    apply IHe; auto.
  - intros n.
    simpl in *.
    f_equal.
    + apply IHe1; auto.
    + apply IHe2; auto.
    + apply IHe3; auto.
  - intros n.
    simpl in *.
    f_equal.
    apply IHe; auto.
  - intros n.
    simpl in *.
    f_equal.
    + apply IHe1; auto.
    + apply IHe2; auto.
  - intros n.
    simpl in *.
    f_equal.
    apply IHe; auto.
Qed.

Lemma subst_open : forall x u e v,
    lc u -> [x ~> u] ({0 ~> v} e) = {0 ~> ([x ~> u] v)}([x ~> u] e).
Proof.
  intros x u e v Hlc.
  generalize dependent 0.
  induction e.
  - intros n.
    simpl. reflexivity.
  - intros n.
    simpl. reflexivity.
  - intros n.
    simpl.
    destruct (a == x).
    + apply open_lc; auto.
    + simpl. auto.
  - intros n0.
    simpl.
    destruct (n0 == n).
    + reflexivity.
    + simpl. reflexivity.
  - auto.
  - intros n.
    simpl.
    f_equal.
    apply IHe.
  - intros n.
    simpl.
    f_equal.
    + apply IHe1.
    + apply IHe2.
    + apply IHe3.
  - intros n.
    simpl.
    f_equal.
    apply IHe.
  - intros n.
    simpl.
    f_equal.
    apply IHe1.
    apply IHe2.
  - intros n.
    simpl.
    f_equal.
    apply IHe.
Qed.    

Notation env := (list (atom * typ)).

Inductive typing : env -> exp -> typ -> Prop :=
| typing_var : forall E (x : atom) T,
    uniq E
    -> binds x T E
    -> typing E (exp_fvar x) T
| typing_zero : forall E,
    uniq E
    -> typing E exp_zero typ_nat
| typing_succ : forall E e,
    typing E e typ_nat
    -> typing E (exp_succ e) typ_nat
| typing_ifz : forall (L : atoms) E num z_branch s_branch t,
    typing E num typ_nat
    -> typing E z_branch t
    -> (forall (x:atom), x `notin` L
                   -> typing ((x ~ typ_nat) ++ E) (open s_branch (exp_fvar x)) t)
    -> typing E (exp_ifz num z_branch s_branch) t
| typing_abs : forall (L : atoms) E exp t1 t2,
    (forall (x:atom), x `notin` L
                 -> typing ((x ~ t1) ++ E) (open exp (exp_fvar x)) t2)
    -> typing E (exp_abs t1 exp) (typ_parr t1 t2)
| typing_app : forall E e1 e2 t1 t2,
    typing E e1 (typ_parr t1 t2)
    -> typing E e2 t1
    -> typing E (exp_app e1 e2) t2
| typing_fix : forall (L : atoms) E exp t,
    (forall (x:atom), x `notin` L
                 -> typing ((x ~ t) ++ E) (open exp (exp_fvar x)) t)
    -> typing E (exp_fix t exp) t.

Lemma typing_uniq : forall E e T,
    typing E e T -> uniq E.
Proof.
  intros E e T H.
  induction H; auto.
  - pick fresh x;
      assert (uniq ((x ~ t1) ++ E)). {
      apply H0; auto.
    }
    solve_uniq.
  - pick fresh x;
      assert (uniq ((x ~ t) ++ E)). {
      apply H0; auto.
    }
    solve_uniq.
Qed.
  
    
Lemma subst_lc : forall x e u,
    lc e -> lc u -> lc ([x ~> u] e).
Proof.
  intros x e u Hlc.
  generalize dependent u.
  induction Hlc; intros u Hlcu.
  - simpl.
    destruct (x0 == x); try constructor; auto.
  - simpl. constructor.
  - simpl. constructor. apply IHHlc; auto.
  - simpl.
    pick fresh y and apply lc_ifz; auto.
    unfold open in *.
    replace (exp_fvar y) with ([x ~> u] exp_fvar y).
    rewrite <- subst_open; auto.
    simpl.
    destruct (y == x).
    + subst. fsetdec.
    + auto.
  - simpl.
    pick fresh y and apply lc_abs; auto.
    unfold open.
    replace (exp_fvar y) with ([x ~> u] exp_fvar y).
    rewrite <- subst_open; auto.
    apply H0; auto.
    simpl.
    destruct (y == x).
    + subst. fsetdec.
    + auto.
  - simpl.
    constructor; auto.
  - simpl.
    pick fresh y and apply lc_fix.
    unfold open.
    replace (exp_fvar y) with ([x ~> u] exp_fvar y).
    rewrite <- subst_open; auto.
    apply H0; auto.
    simpl.
    destruct (y == x).
    + subst. fsetdec.
    + auto.
Qed.

Lemma typing_weakening : forall (E F : env) e T,
    typing E e T ->
    uniq (F ++ E) ->
    typing (F ++ E) e T.
Proof.
Admitted.

Lemma typing_lc : forall E e T,
    typing E e T -> lc e.
Proof.
  intros E e T Htyping.
  induction Htyping.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh x and apply lc_ifz; auto.
  - pick fresh x and apply lc_abs; auto.
  - constructor; auto.
  - pick fresh x and apply lc_fix; auto.
Qed.

Lemma typing_subst_strengthened : forall F E e x u T1 T2,
    typing (F ++ (x ~ T1) ++ E) e T2
    -> typing E u T1
    -> typing (F ++ E) ([x ~> u] e) T2.
Proof.
  intros F E e x u T1 T2 Htyping1 Htyping2.
  remember (F ++ (x ~ T1) ++ E) as G.
  generalize dependent F.
  induction Htyping1.
  - intros F Heq. subst.
    simpl.
    destruct (x0 == x).
    + subst.
      assert (T = T1). {
        eapply binds_mid_eq; eauto.
      }
      subst.
      apply typing_weakening; auto.
      eapply uniq_remove_mid; eauto.
    + apply uniq_remove_mid in H.
      apply binds_remove_mid in H0; auto.
      constructor; auto.
  - intros F Heq. subst.
    simpl.
    apply uniq_remove_mid in H.
    constructor; auto.
  - intros F Heq. subst.
    simpl.
    constructor.
    apply IHHtyping1; auto.
  - intros F Heq. subst.
    simpl.
    pick fresh y and apply typing_ifz; auto.
    unfold open in *.
    replace (exp_fvar y) with ([x ~> u] exp_fvar y).
    rewrite <- subst_open; auto.
    apply H0 with (F0 := (y ~ typ_nat) ++ F); auto.
    eapply typing_lc; eauto.
    simpl.
    destruct (y == x).
    + subst.
      fsetdec.
    + auto.
  - intros F Heq. subst.
    simpl.
    pick fresh y and apply typing_abs.
    unfold open in *.
    replace (exp_fvar y) with ([x ~> u] exp_fvar y).
    rewrite <- subst_open.
    apply H0 with (F0 := (y ~ t1) ++ F); auto.
    eapply typing_lc; eauto.
    simpl.
    destruct (y == x).
    + subst. fsetdec.
    + auto.
  - intros F Heq. subst.
    simpl.
    apply typing_app with (t1 := t1); auto.
  - intros F Heq. subst.
    simpl.
    pick fresh y and apply typing_fix.
    unfold open in *.
    replace (exp_fvar y) with ([x ~> u] exp_fvar y).
    rewrite <- subst_open.
    apply H0 with (F0 := (y ~ t) ++ F); auto.
    eapply typing_lc; eauto.
    simpl.
    destruct (y == x).
    + subst. fsetdec.
    + auto.
Qed.

Lemma typing_subst : forall E e x u T1 T2,
    typing ((x ~ T1) ++ E) e T2
    -> typing E u T1
    -> typing E ([x ~> u] e) T2.
Proof.
  intros.
  rewrite_env (nil ++ E).
  rewrite_env (nil ++ (x ~ T1) ++ E) in H.
  eapply typing_subst_strengthened; eauto.
Qed.
  
(** A strict judgement on what are values *)
Inductive strict_is_val : exp -> Prop :=
| zero_is_val : strict_is_val exp_zero
| succ_is_val : forall e, strict_is_val e -> strict_is_val (exp_succ e)
| abs_is_val : forall t e, lc (exp_abs t e) -> strict_is_val (exp_abs t e).

Inductive strict_small_step : exp -> exp -> nat -> Prop :=
| succ_step : forall e1 e2 k,
    strict_small_step e1 e2 k
    -> strict_small_step (exp_succ e1) (exp_succ e2) k
| ifz_step_num : forall num num' z_branch s_branch k,
    lc (exp_ifz num z_branch s_branch)
    -> strict_small_step num num' k
    -> strict_small_step (exp_ifz num z_branch s_branch)
                        (exp_ifz num' z_branch s_branch)
                        k
| ifz_zero_step : forall z_branch s_branch,
    lc (exp_ifz exp_zero z_branch s_branch)
    -> strict_small_step (exp_ifz exp_zero z_branch s_branch)
                        z_branch 1
| ifz_succ_step : forall num z_branch s_branch,
    lc (exp_ifz (exp_succ num) z_branch s_branch)
    -> strict_is_val (exp_succ num)
    -> strict_small_step (exp_ifz (exp_succ num) z_branch s_branch)
                        (open s_branch num) 1
| app_step_l : forall e1 e1' e2 k,
    lc e2
    -> strict_small_step e1 e1' k
    -> strict_small_step (exp_app e1 e2) (exp_app e1' e2) k
| app_step_r : forall e1 e2 e2' k,
    strict_is_val e1
    -> strict_small_step e2 e2' k
    -> strict_small_step (exp_app e1 e2) (exp_app e1 e2') k
| beta_step : forall e t e2,
    lc (exp_abs t e)
    -> strict_is_val e2
    -> strict_small_step (exp_app (exp_abs t e) e2)
                        (open e e2) 1
| fix_step : forall t e,
    lc (exp_fix t e)
    -> strict_small_step (exp_fix t e)
                        (exp_fix t (open e (exp_fix t e))) 1.

Lemma val_lc : forall e,
    strict_is_val e -> lc e.
Proof.
  intros e Hval.
  induction Hval; try constructor; auto.
Qed.
  
Lemma beta_regular_left : forall e e' k,
    strict_small_step e e' k -> lc e.
Proof.
  intros e e' k Hstep.
  induction Hstep.
  - constructor; auto.
  - inversion H; subst.
    pick fresh x and apply lc_ifz; auto.
  - auto.
  - auto.
  - constructor; auto.
  - constructor; auto.
    apply val_lc in H; auto.
  - inversion H; subst.
    constructor; auto.
    apply val_lc in H0; auto.
  - auto.
Qed.

Lemma beta_regular_right : forall e e' k,
    strict_small_step e e' k -> lc e'.
Proof.
  intros e e' k Hstep.
  induction Hstep.
  - constructor; auto.
  - inversion H; subst.
    pick fresh x and apply lc_ifz; auto.
  - inversion H; subst; auto.
  - inversion H; subst; auto.
    unfold open in *.
    pick fresh x.
    rewrite subst_intro with (x := x); auto.
    apply subst_lc; auto.
    inversion H4; auto.
  - constructor; auto.
  - apply val_lc in H.
    constructor; auto.
  - inversion H; subst.
    unfold open in *.
    pick fresh x.
    rewrite subst_intro with (x := x); auto.
    apply subst_lc; auto.
    apply val_lc in H0; auto.
  - inversion H; subst.
    pick fresh x and apply lc_fix.
    unfold open in *.
    rewrite <- open_lc.
    + pick fresh y.
      rewrite subst_intro with (x := y); auto.
      apply subst_lc.
      apply H1; auto.
      auto.
    + pick fresh y.
      rewrite subst_intro with (x := y); auto.
      apply subst_lc.
      apply H1; auto.
      auto.
Qed.

Lemma beta_regular : forall e e' k,
    strict_small_step e e' k -> lc e /\ lc e'.
Proof.
  intros.
  split.
  eapply beta_regular_left; eauto.
  eapply beta_regular_right; eauto.
Qed.


Lemma canonical_form_abs : forall E e t1 t2,
    typing E e (typ_parr t1 t2)
    -> strict_is_val e
    -> exists e1, e = exp_abs t1 e1.
Proof.
  intros E e t1 t2 Htyping Hval.
  inversion Htyping; subst; try (inversion Hval; subst).
  exists exp0.
  reflexivity.
Qed.
  
Lemma progress : forall e T,
    typing nil e T
    -> strict_is_val e \/ exists e' k, strict_small_step e e' k.
Proof.
  intros e T.
  remember nil as E.
  intros Htyping.
  assert (lc e). {
    eapply typing_lc.
    apply Htyping.
  }
  induction Htyping.
  - subst. apply binds_nil_iff in H1.
    destruct H1.
  - left. constructor.
  - subst.
    destruct IHHtyping; auto.
    + inversion H; auto.
    + left. constructor; auto.
    + destruct H0 as [e' H'].
      destruct H' as [k H0].
      right.
      exists (exp_succ e').
      exists k.
      constructor; auto.
  - subst.
    right.
    destruct IHHtyping1; auto;
      destruct IHHtyping2; auto.
    + inversion H; auto.
    + inversion H; auto.
    + inversion H; auto.
    + inversion H; auto.
    + inversion H2; subst.
      * exists z_branch, 1.
        constructor; auto.
      * Print open.
        exists (open s_branch e), 1.
        constructor; auto.
      * inversion Htyping1; auto.
    + inversion H2; subst.
      * exists z_branch, 1.
        constructor; auto.
      * exists (open s_branch e), 1.
        constructor; auto.
      * inversion Htyping1.
    + inversion H; auto.
    + destruct H2 as [e' H2].
      destruct H2 as [k H2].
      exists (exp_ifz e' z_branch s_branch), k.
      constructor; auto.
    + destruct H2 as [e' H2].
      destruct H2 as [k H2].
      exists (exp_ifz e' z_branch s_branch), k.
      constructor; auto.
  - left.
    constructor; auto.
  - right.
    destruct IHHtyping1; auto;
      destruct IHHtyping2; auto.
    + inversion H; auto.
    + inversion H; auto.
    + inversion H; auto.
    + inversion H; auto.
    + assert (exists e10, e1 = exp_abs t1 e10). {
        eapply canonical_form_abs; eauto.
      }
      destruct H2 as [e10 H2].
      subst.
      exists (open e10 e2), 1.
      constructor.
      apply val_lc; auto.
      auto.
    + destruct H1 as [e' H1].
      destruct H1 as [k H1].
      exists (exp_app e1 e'), k.
      constructor; auto.
    + inversion H; auto.
    + destruct H0 as [e' H0].
      destruct H0 as [k H0].
      exists (exp_app e' e2), k.
      constructor; auto.
      inversion H; auto.
    + destruct H0 as [e' H0].
      destruct H0 as [k H0].
      exists (exp_app e' e2), k.
      constructor; auto.
      inversion H; auto.
  - right.
    exists (exp_fix t (open exp0 (exp_fix t exp0))), 1.
    constructor; auto.
Qed.

Lemma preservation : forall E e e' T k,
    typing E e T
    -> strict_small_step e e' k
    -> typing E e' T.
Proof.
  intros E e e' T k Htyping Hstep.
  generalize dependent E.
  generalize dependent T.
  induction Hstep.
  - intros T E Htyping.
    inversion Htyping; subst.
    constructor; auto.
  - intros T E Htyping.
    inversion Htyping; subst.
    pick fresh x and apply typing_ifz; auto.
  - intros T E Htyping.
    inversion Htyping; auto.
  - intros T E Htyping.
    inversion Htyping; subst.
    unfold open in *.
    pick fresh x.
    rewrite subst_intro with (x := x); auto.
    inversion H5; subst.
    apply typing_subst with (T1 := typ_nat); auto.
  - intros T E Htyping.
    inversion Htyping; subst.
    econstructor; eauto.
  - intros T E Htyping.
    inversion Htyping; subst.
    econstructor; eauto.
  - intros T E Htyping.
    inversion Htyping; subst.
    unfold open in *.
    inversion H4; subst.
    pick fresh x.
    rewrite subst_intro with (x := x); auto.
    eapply typing_subst; eauto.
  - intros T E Htyping.
    inversion Htyping; subst.
    assert (typing E (open e (exp_fix T e)) T). {
      pick fresh x.
      unfold open in *.
      rewrite subst_intro with (x := x); auto.
      apply typing_subst with (T1 := T).
      apply H4; auto.
      auto.
    }
    pick fresh x and apply typing_fix.
    unfold open in *.
    rewrite <- open_lc; auto.
    apply typing_weakening; auto.
    apply typing_uniq in Htyping.
    solve_uniq.
    apply typing_lc in H0; auto.    
Qed.
    
End CallByValue.
Export CallByValue.

Module CallByNeed.

  Inductive lc : exp -> Prop :=
  | lc_sym  : forall x, lc (exp_sym x)
  | lc_blackhole : lc (exp_blackhole)
  | lc_fvar : forall x, lc (exp_fvar x)
  | lc_zero : lc exp_zero
  | lc_succ : forall e, lc e -> lc (exp_succ e)
  | lc_ifz : forall (L : atoms) (num z_branch s_branch : exp),
      lc num
      -> lc z_branch
      -> (forall x, x `notin` L -> lc (open s_branch (exp_fvar x)))
      -> lc (exp_ifz num z_branch s_branch)
  | lc_abs : forall (L : atoms) t exp,
      (forall x, x `notin` L -> lc (open exp (exp_fvar x)))
      -> lc (exp_abs t exp)
  | lc_app : forall e1 e2, lc e1
                      -> lc e2
                      -> lc (exp_app e1 e2)
  | lc_fix : forall (L : atoms) t exp,
      (forall x, x `notin` L -> lc (open exp (exp_fvar x)))
      -> lc (exp_fix t exp).

  Definition mu_table := list (atom * exp).  
  Definition sig_table := list (atom * typ).

  Inductive lc_mu : mu_table -> Prop :=
  | lc_mu_safe : forall mu, uniq mu
                       -> (forall x e, binds x e mu
                                 -> lc e)
                       -> lc_mu mu.

  Definition lc_by_need (e : exp) (mu : mu_table) : Prop :=
    lc e /\ lc_mu mu.
  
  Inductive cbn_is_val : exp -> sig_table -> Prop :=
  | cbn_is_val_zero : forall Σ, uniq Σ -> cbn_is_val exp_zero Σ
  | cbn_is_val_succ : forall a Σ, uniq Σ ->
                             binds a typ_nat Σ ->
                             cbn_is_val (exp_succ (exp_sym a)) Σ
  | cbn_is_val_abs : forall t e Σ, uniq Σ -> cbn_is_val (exp_abs t e) Σ.

  Inductive typing : env -> sig_table -> exp -> typ -> Prop :=
  | typing_sym : forall E (a : atom) T Σ,
      uniq E
      -> uniq Σ
      -> binds a T Σ
      -> typing E Σ (exp_sym a) T
  | typing_var : forall E (x : atom) T Σ,
      uniq E
      -> binds x T E
      -> typing E Σ (exp_fvar x) T
  | typing_zero : forall E Σ,
      uniq E
      -> typing E Σ exp_zero typ_nat
  | typing_succ : forall E e Σ,
      typing E Σ e typ_nat
      -> typing E Σ (exp_succ e) typ_nat
  | typing_ifz : forall (L : atoms) E num z_branch s_branch t Σ,
      typing E Σ num typ_nat
      -> typing E Σ z_branch t
      -> (forall (x:atom), x `notin` L
                     -> typing ((x ~ typ_nat) ++ E) Σ (open s_branch (exp_fvar x)) t)
      -> typing E Σ (exp_ifz num z_branch s_branch) t
  | typing_abs : forall (L : atoms) E exp t1 t2 Σ,
      (forall (x:atom), x `notin` L
                   -> typing ((x ~ t1) ++ E) Σ (open exp (exp_fvar x)) t2)
      -> typing E Σ (exp_abs t1 exp) (typ_parr t1 t2)
  | typing_app : forall E e1 e2 t1 t2 Σ,
      typing E Σ e1 (typ_parr t1 t2)
      -> typing E Σ e2 t1
      -> typing E Σ (exp_app e1 e2) t2
  | typing_fix : forall (L : atoms) E exp t Σ,
      (forall (x:atom), x `notin` L
                   -> typing ((x ~ t) ++ E) Σ (open exp (exp_fvar x)) t)
      -> typing E Σ (exp_fix t exp) t.

  Lemma typing_not_blackhole : forall E Σ e T,
      typing E Σ e T -> e <> exp_blackhole.
  Proof.
    intros E Σ e T Htyping contra.
    induction Htyping; try inversion contra.
  Qed.
  
  Locate "`notin`".
  Locate "`in`".
  
  Inductive typing_mu : sig_table -> mu_table -> sig_table -> Prop :=
  | typing_mu_safe : forall Σ' Σ mu, uniq Σ'
                               -> uniq Σ
                               -> uniq mu
                               -> (forall a t, binds a t Σ
                                         -> exists e, binds a e mu
                                                /\ (e <> exp_blackhole
                                                   -> typing nil Σ' e t))
                               -> typing_mu Σ' mu Σ.
  
  Definition eval_state := (sig_table * exp * mu_table) % type.

  Inductive eval_state_ok : eval_state -> Prop :=
  | eval_state_safe : forall Σ e t mu, typing nil Σ e t
                                  -> typing_mu Σ mu Σ
                                  -> eval_state_ok (Σ, e, mu).
  
  Inductive cbn_smallstep : eval_state -> eval_state -> nat -> Prop :=
  | cbn_smallstep_lookup :
      forall e Σ a T mu,
        lc_by_need (exp_sym a) mu
        -> uniq Σ
        -> binds a T Σ
        -> uniq mu
        -> binds a e mu
        -> e <> exp_blackhole
        -> cbn_smallstep (Σ, (exp_sym a), mu) (Σ, e, mu) 1
  | cbn_smallstep_inplace :
      forall e e' Σ Σ' a T mu_l mu_r mu_l' mu_r' k,
        lc_by_need e (mu_l ++ mu_r)
        -> uniq (mu_l ++ (a ~ exp_blackhole) ++ mu_r)
        -> uniq Σ
        -> binds a T Σ
        -> binds a T Σ'
        -> cbn_smallstep (Σ, e, mu_l ++ (a ~ exp_blackhole) ++ mu_r)
                        (Σ', e', mu_l' ++ (a ~ exp_blackhole) ++ mu_r') k
        -> e <> exp_blackhole
        -> e' <> exp_blackhole
        -> cbn_smallstep (Σ, (exp_sym a), mu_l ++ (a ~ e) ++ mu_r)
                        (Σ', (exp_sym a), mu_l' ++ (a ~ e') ++ mu_r') k
  | cbn_smallstep_succ :
      forall e Σ_l Σ_r mu_l mu_r a,
        lc_by_need (exp_succ e) (mu_l ++ mu_r)
        -> e <> exp_blackhole
        -> uniq (Σ_l ++ (a ~ typ_nat) ++ Σ_r)
        -> uniq (mu_l ++ (a ~ e) ++ mu_r)
        -> cbn_smallstep (Σ_l ++ Σ_r,
                         exp_succ e,
                         mu_l ++ mu_r)
                        (Σ_l ++ (a ~ typ_nat) ++ Σ_r,
                         exp_succ (exp_sym a),
                         mu_l ++ (a ~ e) ++ mu_r) 1
  | cbn_smallstep_ifz_num :
      forall e e' Σ Σ' mu mu' z_branch s_branch k,
        lc_by_need (exp_ifz e z_branch s_branch) mu
        -> cbn_smallstep (Σ, e, mu)
                      (Σ', e', mu') k
        -> cbn_smallstep (Σ, exp_ifz e z_branch s_branch, mu)
                        (Σ', exp_ifz e' z_branch s_branch, mu') k
  | cbn_smallstep_ifz_zero :
      forall Σ mu z_branch s_branch,
        lc_by_need (exp_ifz exp_zero z_branch s_branch) mu
        -> uniq Σ
        -> uniq mu
        -> cbn_smallstep (Σ, exp_ifz exp_zero z_branch s_branch, mu) (Σ, z_branch, mu) 1
  | cbn_smallstep_ifz_succ :
      forall e a Σ z_branch s_branch mu,
        lc_by_need (exp_ifz (exp_succ (exp_sym a)) z_branch s_branch) mu
        -> binds a typ_nat Σ
        -> binds a e mu
        -> uniq Σ
        -> cbn_smallstep (Σ, exp_ifz (exp_succ (exp_sym a)) z_branch s_branch, mu)
                        (Σ, open s_branch (exp_sym a), mu) 1
  | cbn_smallstep_app_l :
      forall e1 e1' e2 Σ Σ' mu mu' k,
        lc_by_need (exp_app e1 e2) mu
        -> cbn_smallstep (Σ, e1, mu)
                        (Σ', e1', mu') k
        -> cbn_smallstep (Σ, exp_app e1 e2, mu)
                        (Σ', exp_app e1' e2, mu') k
  | cbn_smallstep_beta :
      forall Σ_l Σ_r t a e e2 mu_l mu_r,
        lc_by_need (exp_app (exp_abs t e) e2) (mu_l ++ mu_r)
        -> uniq (Σ_l ++ (a ~ t) ++ Σ_r)
        -> uniq (mu_l ++ (a ~ e2) ++ mu_r)
        -> e2 <> exp_blackhole
        -> cbn_smallstep (Σ_l ++ Σ_r, exp_app (exp_abs t e) e2, mu_l ++ mu_r)
                        (Σ_l ++ (a ~ t) ++ Σ_r, open e (exp_sym a), mu_l ++ (a ~ e2) ++ mu_r) 1
  | cbn_smallstep_fix :
      forall Σ_l Σ_r t e mu_l mu_r a,
        lc_by_need (exp_fix t e) (mu_l ++ mu_r)
        -> uniq (Σ_l ++ (a ~ t) ++ Σ_r)
        -> uniq (mu_l ++ (a ~ (open e (exp_sym a))) ++ mu_r)
        -> e <> exp_blackhole
        -> cbn_smallstep (Σ_l ++ Σ_r,
                         exp_fix t e,
                         mu_l ++ mu_r)
                        (Σ_l ++ (a ~ t) ++ Σ_r,
                         exp_sym a,
                         mu_l ++ (a ~ (open e (exp_sym a))) ++ mu_r) 1.


  Ltac solve_open_lc_main :=
    match goal with
      H : forall x : atom,
        x `notin` ?L
        -> forall k, open ?exp (exp_fvar x) = {k ~> ?u} open ?exp (exp_fvar x)
               |- _ => unfold open in H;
                     pick fresh x;
                     apply open_lc_core with (j := 0) (v := exp_fvar x);
                     try (apply H);
                     auto
    end.
  
  Lemma open_lc : forall (k : nat) (u e : exp), lc e -> e = {k ~> u} e.
  Proof.
    intros k u e Hlc.
    generalize dependent k.
    induction Hlc; try (simpl; reflexivity).
    - intros k.
      simpl.
      rewrite <- IHHlc.
      reflexivity.
    - intros k.
      simpl.
      rewrite <- IHHlc1.
      rewrite <- IHHlc2.
      f_equal.
      solve_open_lc_main.
    - intros k.
      simpl.
      f_equal.
      solve_open_lc_main.
    - intros k.
      simpl.
      rewrite <- IHHlc1.
      rewrite <- IHHlc2.
      reflexivity.
    - intros k.
      simpl.
      f_equal.
      solve_open_lc_main.
  Qed.

  Lemma subst_open : forall x u e v,
      lc u -> [x ~> u] ({0 ~> v} e) = {0 ~> ([x ~> u] v)}([x ~> u] e).
  Proof.
    intros x u e v Hlc.
    generalize dependent 0.
    induction e.
    - intros n.
      simpl. reflexivity.
    - intros n.
      simpl. reflexivity.
    - intros n.
      simpl.
      destruct (a == x).
      + apply open_lc; auto.
      + simpl. auto.
    - intros n0.
      simpl.
      destruct (n0 == n).
      + reflexivity.
      + simpl. reflexivity.
    - auto.
    - intros n.
      simpl.
      f_equal.
      apply IHe.
    - intros n.
      simpl.
      f_equal.
      + apply IHe1.
      + apply IHe2.
      + apply IHe3.
    - intros n.
      simpl.
      f_equal.
      apply IHe.
    - intros n.
      simpl.
      f_equal.
      apply IHe1.
      apply IHe2.
    - intros n.
      simpl.
      f_equal.
      apply IHe.
  Qed.
  
  Lemma subst_lc : forall x e u,
      lc e -> lc u -> lc ([x ~> u] e).
  Proof.
    intros x e u Hlc.
    generalize dependent u.
    induction Hlc; intros u Hlcu.
    - simpl. constructor.
    - simpl. constructor.
    - simpl.
      destruct (x0 == x); try constructor; auto.
    - simpl. constructor.
    - simpl. constructor. apply IHHlc; auto.
    - simpl.
      pick fresh y and apply lc_ifz; auto.
      unfold open in *.
      replace (exp_fvar y) with ([x ~> u] exp_fvar y).
      rewrite <- subst_open; auto.
      simpl.
      destruct (y == x).
      + subst. fsetdec.
      + auto.
    - simpl.
      pick fresh y and apply lc_abs; auto.
      unfold open.
      replace (exp_fvar y) with ([x ~> u] exp_fvar y).
      rewrite <- subst_open; auto.
      apply H0; auto.
      simpl.
      destruct (y == x).
      + subst. fsetdec.
      + auto.
    - simpl.
      constructor; auto.
    - simpl.
      pick fresh y and apply lc_fix.
      unfold open.
      replace (exp_fvar y) with ([x ~> u] exp_fvar y).
      rewrite <- subst_open; auto.
      apply H0; auto.
      simpl.
      destruct (y == x).
      + subst. fsetdec.
      + auto.
  Qed.

  Lemma typing_subst : forall Σ E e x u T1 T2,
      typing ((x ~ T1) ++ E) Σ e T2 ->
      typing E Σ u T1 ->
      typing E Σ ([x ~> u] e) T2.
  Proof.
    Admitted.

  Lemma beta_regular_left : forall Σ Σ' e e' mu mu' k,
      cbn_smallstep (Σ, e, mu)
                    (Σ', e', mu') k
      -> lc_by_need e mu.
  Proof.
    intros.
    remember (Σ, e, mu) as start_st.
    induction H; inversion Heqstart_st; destruct H; split; subst; auto.
    - constructor.
    - constructor.
      rewrite_env (mu_l ++ (a ~ e0) ++ mu_r).
      solve_uniq.
      rewrite_env (mu_l ++ (a ~ e0) ++ mu_r).
      intros.
      inversion H7; subst.
      destruct (x == a).
      + subst.
        assert (e = e0). {
          eapply binds_mid_eq; eauto.
          solve_uniq.
        }
        subst.
        auto.
      + apply H10 with (x := x).
        eapply binds_remove_mid; eauto.
  Qed.

  Lemma beta_regular_right : forall Σ Σ' e e' mu mu' k,
      cbn_smallstep (Σ, e, mu)
                    (Σ', e', mu') k
      -> lc_by_need e' mu'.
  Proof.
    intros.
    remember (Σ, e, mu) as start_st.
    remember (Σ', e', mu') as target_st.
    generalize dependent mu.
    generalize dependent mu'.
    generalize dependent e.
    generalize dependent e'.
    induction H.
    - intros e' e0 mu' Heqtarget_st mu0 Heqstart_st. 
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      inversion H; subst.
      split; auto.
      inversion H6; subst.
      eapply H8; eauto.
    - intros e1 e0 mu' Heqtarget_st mu Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      inversion H; subst.
      split; auto.
      + constructor.
      + edestruct IHcbn_smallstep with (mu' := mu_l' ++ (a ~ exp_blackhole) ++ mu_r')
                                         (mu  := mu_l ++ (a ~ exp_blackhole) ++ mu_r).
        reflexivity.
        reflexivity.
        inversion H10; subst.
        constructor.
        * solve_uniq.
        * intros.
          {
            destruct (x == a). 
            - subst.
              simpl_env in H13.
              assert (e0 = e'). {
                eapply binds_mid_eq; eauto.
                solve_uniq.
              }
              subst.
              auto.
            - apply H12 with (x := x).
              apply binds_remove_mid in H13; auto.
          }
    - intros e1 e0 mu' Heqtarget_st mu Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      inversion H; subst.
      split.
      + repeat constructor.
      + inversion H4; subst.
        constructor.
        * solve_uniq.
        * intros.
          simpl_env in H7.
          {
            destruct (x == a).
            - subst.
              assert (e0 = e). {
                eapply binds_mid_eq; eauto.
              }
              subst.
              inversion H3; auto.
            - apply H6 with (x := x).
              apply binds_remove_mid in H7; auto.
          }
    - intros e1 e0 mu1 Heqtarget_st mu0 Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      inversion H; subst.
      split.
      + inversion H1; subst.
        pick fresh x and apply lc_ifz; auto.
        edestruct IHcbn_smallstep.
        reflexivity.
        reflexivity.
        auto.
      + edestruct IHcbn_smallstep.
        reflexivity.
        reflexivity.
        auto.
    - intros e1 e0 mu' Heqtarget_st mu0 Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      inversion H; subst.
      split; auto.
      inversion H2; subst; auto.
    - intros e1 e0 mu' Heqtarget_st mu0 Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      inversion H; subst.
      split; auto.
      inversion H3; subst.
      pick fresh x.
      unfold open.
      rewrite subst_intro with (x := x); auto.
      apply subst_lc; auto.
      apply H10; auto.
      constructor.
    - intros e' e mu1 Heqtarget_st mu0 Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      inversion H; subst.
      split; auto.
      * inversion H1; subst.
        edestruct IHcbn_smallstep.
        reflexivity.
        reflexivity.
        constructor; auto.
      * edestruct IHcbn_smallstep.
        reflexivity.
        reflexivity.
        auto.
    - intros e1 e0 mu1 Heqtarget_st mu Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      split; auto.
      * inversion H; subst.
        inversion H3; subst.
        inversion H7; subst.
        pick fresh x.
        unfold open.
        rewrite subst_intro with (x := x); auto.
        apply subst_lc; auto.
        apply H6; auto.
        constructor.
      * inversion H; subst.
        simpl_env.
        constructor.
        solve_uniq.
        intros.
        {
          destruct (x == a).
          - subst.
            assert (e0 = e2). {
              eapply binds_mid_eq; eauto.
            }
            subst.
            inversion H3; subst; auto.
          - inversion H4; subst.
            apply H7 with (x := x); auto.
            apply binds_remove_mid in H5; auto.
        }
    - intros e1 e0 mu1 Heqtarget_st mu0 Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      inversion H; subst.
      split; auto.
      + constructor.
      + simpl_env.
        constructor.
        * solve_uniq.
        * intros.
          {
            destruct (x == a).
            - subst.
              assert (e0 = open e (exp_sym a)). {
                eapply binds_mid_eq; eauto.
              }
              subst.
              inversion H3; subst.
              unfold open.
              pick fresh x.
              rewrite subst_intro with (x := x); auto.
              apply subst_lc; try constructor.
              apply H7; auto.
            - inversion H4; subst.
              apply H7 with (x := x).
              apply binds_remove_mid in H5; auto.
          }
  Qed.

  Lemma beta_regular : forall Σ Σ' e e' mu mu' k,
      cbn_smallstep (Σ, e, mu) (Σ', e', mu') k
      -> lc_by_need e mu /\ lc_by_need e' mu'.
  Proof.
    intros.
    split.
    eapply beta_regular_left; eauto.
    eapply beta_regular_right; eauto.
  Qed.

  Lemma step_uniq_left : forall Σ Σ' e e' mu mu' k,
      cbn_smallstep (Σ, e, mu) (Σ', e', mu') k
      -> uniq Σ.
  Proof.
    intros Σ Σ' e e' mu mu' k Hstep.
    remember (Σ, e, mu) as start_st.
    remember (Σ', e', mu') as target_st.
    generalize dependent Σ.
    generalize dependent Σ'.
    generalize dependent e.
    generalize dependent e'.
    generalize dependent mu.
    generalize dependent mu'.
    induction Hstep;
      intros;
      inversion Heqstart_st;
      inversion Heqtarget_st;
      subst;
      try solve_uniq.
    - eapply IHHstep.
      reflexivity.
      reflexivity.
    - eapply IHHstep.
      reflexivity.
      reflexivity.
  Qed.

  Lemma step_uniq_right : forall Σ Σ' e e' mu mu' k,
      cbn_smallstep (Σ, e, mu) (Σ', e', mu') k
      -> uniq Σ'.
  Proof.
    intros Σ Σ' e e' mu mu' k Hstep.
    remember (Σ, e, mu) as start_st.
    remember (Σ', e', mu') as target_st.
    generalize dependent Σ.
    generalize dependent Σ'.
    generalize dependent e.
    generalize dependent e'.
    generalize dependent mu.
    generalize dependent mu'.
    induction Hstep;
      intros;
      inversion Heqstart_st;
      inversion Heqtarget_st;
      subst;
      subst; try solve_uniq.
    - eapply IHHstep.
      reflexivity.
      reflexivity.
    - eapply IHHstep.
      reflexivity.
      reflexivity.
    - eapply IHHstep.
      reflexivity.
      reflexivity.
  Qed.

  Lemma step_uniq : forall Σ Σ' e e' mu mu' k,
      cbn_smallstep (Σ, e, mu) (Σ', e', mu') k
      -> uniq Σ /\ uniq Σ'.
  Proof.
    intros.
    split.
    eapply step_uniq_left; eauto.
    eapply step_uniq_right; eauto.
  Qed.

  Definition sigma_subset (Σ Σ' : sig_table) :=
    forall a t, binds a t Σ -> binds a t Σ'.

  Notation "z ⊆ z2" := (sigma_subset z z2) (at level 50, no associativity).

  Lemma sigma_subset_reflexive : forall Σ,
      Σ ⊆ Σ.
  Proof.
    intros Σ Hbind. auto.
  Qed.

  Hint Resolve sigma_subset_reflexive.

  Lemma typing_weakening_sigma : forall E Σ_l Σ_r a e t t2,
      typing E (Σ_l ++ Σ_r) e t ->
      uniq (Σ_l ++ (a ~ t2) ++ Σ_r) ->
      typing E (Σ_l ++ (a ~ t2) ++ Σ_r) e t.
  Proof.
  Admitted.

  Lemma typing_weakening_sigma_strengthened : forall E Σ Σ' e t,
      Σ ⊆ Σ' ->
      uniq Σ' ->
      typing E Σ e t ->
      typing E Σ' e t.
  Proof.
  Admitted.
  
  Lemma preservation_strengthened : forall Σ Σ' e e' mu mu' t k,
      cbn_smallstep (Σ, e, mu) (Σ', e', mu') k
      -> typing_mu Σ mu Σ
      -> typing nil Σ e t
      -> typing_mu Σ' mu' Σ' /\ typing nil Σ' e' t /\ Σ ⊆ Σ'.
  Proof.
    intros Σ Σ' e e' mu mu' t k Hstep Htyping_mu Htyping_e.
    remember (Σ, e, mu) as start_st.
    remember (Σ', e', mu') as target_st.
    generalize dependent Σ.
    generalize dependent Σ'.
    generalize dependent mu.
    generalize dependent mu'.
    generalize dependent e.
    generalize dependent e'.
    generalize dependent t.
    induction Hstep.
    - Case "Lookup".
      intros t e1 e0 mu1 m0 Σ1 Heqtarget_st Σ0 Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      intros Htyping_mu0 Htyping_a.
      subst.
      split.
      + auto.
      + inversion Htyping_mu0; subst.
        inversion Htyping_a; subst.
        split; auto.
        * destruct (H8 a t H14) as [e' H15].
          destruct H15.
          assert (e' = e1). {
            eapply binds_unique; eauto.
          }
          subst.
          apply H12; auto.
    - Case "InPlace".
      intros t e1 e0 mu1 m0 Σ1 Heqtarget_st Σ0 Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      intros Htyping_mu0 Htyping_a.
      simpl_env in *.
      inversion Htyping_mu0; subst.
      inversion Htyping_a; subst.
      assert (uniq Σ1). {
        eapply step_uniq_right; eauto.
      }
      {
        edestruct IHHstep as [Htyping_mu' [Htyping_e1 Hsubset]]; eauto.
        - SCase "Typing mu with blackhole".
          constructor; auto.
          intros a0 t0 Hbinds_a0.
          destruct (a0 == a).
          + SSCase "a0 = a".
            subst.
            exists exp_blackhole.
            split; auto.
            intros; solve_neq_contra.
          + SSCase "a0 <> a".
            destruct (H9 a0 t0 Hbinds_a0) as [e0 [Hbinds_e0 Htyping_e0]].
            exists e0.
            split; auto.
            * eapply binds_remove_mid in Hbinds_e0; eauto.
        - SCase "Typing e".
          destruct (H9 a t H15) as [e0 [Hbinds_e0 Htyping_e0]].
          assert (e0 = e). {
            eapply binds_unique; eauto.
          }
          subst.
          apply Htyping_e0; auto.
        - SCase "Goal".
          split; split; auto.
          inversion Htyping_mu'; subst.
          solve_uniq.
          intros.
          inversion Htyping_mu'; subst.
          destruct (a0 == a).
          + subst.
            assert (binds a t Σ1). {
              apply Hsubset; auto.
            }
            assert (t0 = t). {
              eapply binds_unique; eauto.
            }
            subst.
            exists e'.
            split; auto.
          + destruct (H18 a0 t0 H13) as [e2 [Hbinds_e2 Htyping_e2]].
            exists e2.
            split.
            * apply binds_remove_mid in Hbinds_e2; auto.
            * auto.
          + constructor; auto.
      }
    - Case "Succ".
      intros t e1 e0 mu1 m0 Σ1 Heqtarget_st Σ0 Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      intros Htyping_mu0 Htyping_e0.
      clear Heqstart_st. clear Heqtarget_st.
      inversion Htyping_mu0; subst.
      inversion Htyping_e0; subst.
      simpl_env in *.
      split.
      + SCase "Type mu".
        constructor; auto.
        intros.
        destruct (a0 == a).
        * subst.
          assert (t = typ_nat). {
            eapply binds_mid_eq; eauto.
          }
          exists e.
          split; auto.
          intros.
          subst.
          inversion Htyping_e0; subst.
          apply typing_weakening_sigma; auto.
        * apply binds_remove_mid in H7; auto.
          destruct (H6 a0 t H7) as [e1 [Hbinds_e1 Htyping_e1]].
          exists e1.
          split; auto.
          intros.
          apply typing_weakening_sigma; auto.
      + split.
        * constructor.
          constructor; auto.
        * intros x t Hbinds.
          auto.
    - Case "ifz".
      intros t e1 e0 mu1 m0 Σ1 Heqtarget_st Σ0 Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      intros Htyping_mu0 Htyping_e0.
      clear Heqstart_st. clear Heqtarget_st.
      inversion Htyping_e0; subst.
      inversion Htyping_mu0; subst.
      simpl_env in *.
      assert (typing_mu Σ1 mu1 Σ1 /\ typing nil Σ1 e' typ_nat /\ Σ0 ⊆ Σ1). {
        eapply IHHstep; eauto.
      }
      destruct H4.
      destruct H6.
      split; auto.
      split; auto.
      pick fresh x and apply typing_ifz; auto.
      eapply typing_weakening_sigma_strengthened; eauto.
      eapply step_uniq_right; eauto.
      apply typing_weakening_sigma_strengthened with (Σ := Σ0); auto.
      eapply step_uniq_right; eauto.
    - Case "ifz_zero".
      intros t e1 e0 mu1 m0 Σ1 Heqtarget_st Σ0 Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      intros Htyping_mu0 Htyping_e0.
      clear Heqstart_st. clear Heqtarget_st.
      inversion Htyping_e0; subst.
      inversion Htyping_mu0; subst.
      split; auto.
    - Case "ifz_succ".
      intros t e1 e0 mu1 m0 Σ1 Heqtarget_st Σ0 Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      intros Htyping_mu0 Htyping_e0.
      clear Heqstart_st. clear Heqtarget_st.
      inversion Htyping_e0; subst.
      inversion Htyping_mu0; subst.
      inversion H10; subst.
      split; auto.
      split; auto.
      unfold open.
      pick fresh x.
      rewrite subst_intro with (x := x); auto.
      eapply typing_subst; eauto.
    - Case "app_left".
      intros t e3 e0 mu3 m0 Σ3 Heqtarget_st Σ0 Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      intros Htyping_mu0 Htyping_e0.
      clear Heqstart_st. clear Heqtarget_st.
      inversion Htyping_mu0; subst.
      inversion Htyping_e0; subst.
      assert (typing_mu Σ3 mu3 Σ3 /\ typing nil Σ3 e1' (typ_parr t1 t) /\ Σ0 ⊆ Σ3). {
        eapply IHHstep; eauto.
      }
      destruct H4.
      destruct H5.
      split; auto.
      split; auto.
      econstructor; eauto.
      eapply typing_weakening_sigma_strengthened; eauto.
      eapply step_uniq_right; eauto.
    - Case "beta".
      intros T e3 e0 mu3 m0 Σ3 Heqtarget_st Σ0 Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      intros Htyping_mu0 Htyping_e0.
      clear Heqstart_st. clear Heqtarget_st.
      inversion Htyping_mu0; subst.
      inversion Htyping_e0; subst.
      inversion H11; subst.
      simpl_env in *.
      split; auto.
      + constructor; auto.
        intros.
        destruct (a0 == a).
        * subst.
          exists e2.
          split; auto.
          subst.
          assert (t = t1). {
            eapply binds_mid_eq; eauto.
          }
          subst.
          intros.
          eapply typing_weakening_sigma; eauto.
        * apply binds_remove_mid in H7; auto.
          destruct (H6 a0 t H7) as [e1 [Hbinds_e1 Htyping_e1]].
          exists e1.
          split; auto.
          intros.
          apply typing_weakening_sigma; auto.
      + split; auto.
        * unfold open in *.
          pick fresh x.
          rewrite subst_intro with (x := x); auto.
          apply typing_subst with (T1 := t1); auto.
          apply typing_weakening_sigma; auto.
          constructor; auto.
        * intros.
          intros z1 z2 Hsubset.
          apply binds_weaken; auto.
    - Case "fixpoint".
      intros T e3 e0 mu3 m0 Σ3 Heqtarget_st Σ0 Heqstart_st.
      inversion Heqtarget_st; inversion Heqstart_st; subst.
      intros Htyping_mu0 Htyping_e0.
      clear Heqstart_st. clear Heqtarget_st.
      inversion Htyping_mu0; subst.
      inversion Htyping_e0; subst.
      simpl_env in *.
      split; auto.
      + constructor; auto.
        intros.
        destruct (a0 == a).
        * subst.
          assert (t = T). {
            eapply binds_mid_eq; eauto.
          }
          subst.
          exists (open e (exp_sym a)).
          split; auto.
          intros.
          unfold open in *.
          pick fresh x.
          rewrite subst_intro with (x := x); auto.
          apply typing_subst with (T1 := T); auto.
          apply typing_weakening_sigma; auto.
          constructor; auto.
        * apply binds_remove_mid in H7; auto.
          destruct (H6 a0 t H7) as [e1 [Hbinds_e1 Htyping_e1]].
          exists e1.
          split; auto.
          intros.
          apply typing_weakening_sigma; auto.
      + split; auto.
        constructor; auto.
        intros z1 z2 Hsubset.
        apply binds_weaken; auto.
  Qed.
          
  Lemma preservation : forall Σ Σ' e e' mu mu' k,
      cbn_smallstep (Σ, e, mu) (Σ', e', mu') k
      -> eval_state_ok (Σ, e, mu)
      -> eval_state_ok (Σ', e', mu').
  Proof.
    intros.
    inversion H0; subst.
    eapply preservation_strengthened in H; eauto.
    destruct H.
    destruct H1.
    econstructor; eauto.
  Qed.

  Inductive cbn_loop : eval_state -> Prop :=
  | cbn_loop_sym : forall Σ a t mu,
      lc_mu mu ->
      uniq Σ ->
      binds a t Σ ->
      binds a exp_blackhole mu ->
      cbn_loop (Σ, exp_sym a, mu)
  | cbn_loop_circular_exp : forall e Σ a t mu_l mu_r,
      lc_by_need e (mu_l ++ (a ~ exp_blackhole) ++ mu_r) ->
      binds a t Σ ->
      cbn_loop (Σ, e, mu_l ++ (a ~ exp_blackhole) ++ mu_r) ->
      cbn_loop (Σ, exp_sym a, mu_l ++ (a ~ e) ++ mu_r)
  | cbn_loop_ifz : forall e Σ mu z_branch s_branch,
      lc_by_need (exp_ifz e z_branch s_branch) mu ->
      cbn_loop (Σ, e, mu) ->
      cbn_loop (Σ, exp_ifz e z_branch s_branch, mu)
  | cbn_loop_app : forall e1 e2 Σ mu,
      lc_by_need (exp_app e1 e2) mu ->
      cbn_loop (Σ, e1, mu) ->
      cbn_loop (Σ, exp_app e1 e2, mu).

  Inductive cbn_eval_state_initial : eval_state -> Prop :=
  | cbn_eval_state_initial_constr : forall e,
      lc e -> cbn_eval_state_initial (nil, e, nil).

  Inductive cbn_eval_state_final : eval_state -> Prop :=
  | cbn_eval_state_final_constr : forall Σ e mu,
      lc_by_need e mu ->
      uniq Σ ->
      cbn_is_val e Σ ->
      cbn_eval_state_final (Σ, e, mu).

  Lemma typing_exp_lc : forall E Σ e t,
      typing E Σ e t -> lc e.
  Proof.
    intros E Σ e t Htyping.
    induction Htyping; try constructor; auto.
    - pick fresh x and apply lc_ifz; auto.
    - pick fresh x and apply lc_abs; auto.
    - pick fresh x and apply lc_fix; auto.
  Qed.

  (*
  Lemma typing_mu_lc : forall Σ mu,
      typing_mu Σ mu Σ -> lc_mu mu.
  Proof.
    intros Σ mu Htyping.
    inversion Htyping; subst.
    constructor; auto.
    intros.
    Print lc_mu.
    destruct (e == exp_blackhole).
*)

  (*
  Lemma progress : forall Σ e mu,
      eval_state_ok (Σ, e, mu) ->
      cbn_eval_state_final (Σ, e, mu) \/
      cbn_loop (Σ, e, mu) \/
      exists Σ' e' mu' k, cbn_smallstep (Σ, e, mu) (Σ', e', mu') k.
  Proof.
    intros Σ e mu Hok.
    remember (Σ, e, mu) as start_st.
    generalize dependent Σ.
    generalize dependent e.
    generalize dependent mu.
    inversion Hok; subst.
    induction H.
    - intros mu0 e0 Σ0 Heqstart_st.
      inversion Heqstart_st; subst.
      inversion H0; subst.
      inversion Hok; subst.
      inversion H9; subst.
      inversion H11; subst.
*)
      
End CallByNeed.