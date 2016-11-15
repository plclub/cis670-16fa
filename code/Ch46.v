Add LoadPath ".".
Add LoadPath "/Users/sweirich/github/deepspec/metalib/" as Metalib.
Require Import Metalib.Metatheory.

Require Import systemt_inf.
Require Import Ch9.

(* This part of a development for chapter 46. I didn't have time to 
   fill in all of the details, but it should make most of the 
   chapter clear *)

(* ------------ Observable equivalence -------------------- *)

(* These are contexts --- basically we can consider them as terms 
   with a "hole" in them. *)
Inductive ctx : Set :=
| ctx_top  : ctx    (* written  \circ in PFPL *)
| ctx_s    : ctx -> ctx
| ctx_rec1 : ctx -> exp -> atom -> atom -> typ -> exp -> ctx
| ctx_rec2 : exp -> ctx -> atom -> atom -> typ -> exp -> ctx
| ctx_rec3 : exp -> exp -> atom -> atom -> typ -> ctx -> ctx
| ctx_abs  : typ -> atom -> ctx -> ctx
| ctx_app1 : ctx -> exp -> ctx
| ctx_app2 : exp -> ctx -> ctx.

Notation close := close_exp_wrt_exp.

(* Written C { e } in PFPL *)
Fixpoint replace (C : ctx) (e : exp) :=
  match C with
  | ctx_top => e
  | ctx_s C => s (replace C e)
  | ctx_rec1 C e1 x y t e2 => rec (replace C e) e1 (close x (abs t (close y e2)))
  | ctx_rec2 e0 C x y t e2 => rec e0 (replace C e) (close x (abs t (close y e2)))
  | ctx_rec3 e0 e1 x y t C => rec e0 e1 (close x (abs t (close y (replace C e))))
  | ctx_abs t x C => abs t (close x (replace C e))
  | ctx_app1 C e2 => app (replace C e) e2
  | ctx_app2 e1 C => app e1 (replace C e)
  end.

(* Written   C : G |> t ~> G' |> t' *)
Inductive typing_ctx : ctx -> env -> typ -> env -> typ -> Prop :=
| typing_ctx_top : forall G t, typing_ctx ctx_top G t G t
| typing_ctx_s   : forall G t G' C,
    typing_ctx C G t G' typ_nat ->
    typing_ctx (ctx_s C) G t G' typ_nat
| typing_ctx_rec1 : forall C G t G' t' x y e0 e1,
    typing_ctx C G t G' typ_nat ->
    typing G' e0 t' ->
    value e1 -> 
    typing ((y ~ t') ++ (x ~ typ_nat) ++ G') e1  t' ->
    typing_ctx (ctx_rec1 C e0 x y t' e1) G t G' t'
| typing_ctx_rec2 : forall C G t G' t' x y e0 e1,
    typing G' e0 typ_nat ->
    typing_ctx C G t G' t' ->
    value e1 ->
    typing ((y ~ t') ++ (x ~ typ_nat) ++ G') e1 t' ->
    typing_ctx (ctx_rec2 e0 C x y t' e1) G t G' t'
| typing_ctx_rec3 : forall C G t G' t' x y e0 e1,
    typing G' e0 typ_nat ->
    typing G' e1 t' ->
    typing_ctx C G t ((y ~ t') ++ (x ~ typ_nat) ++ G') t' ->
    typing_ctx (ctx_rec3 e0 e1 x y t' C) G t G' t'
| typing_ctx_abs : forall C G G' t t1 t2 x,
    typing_ctx C G t ((x ~ t1) ++ G') t2 ->
    typing_ctx (ctx_abs t1 x C) G t G' (typ_arr t1 t2)
| typing_ctx_app1 : forall C G G' t t2 t' e2,
    typing_ctx C G t G' (typ_arr t2 t') ->
    typing G' e2 t2 ->
    typing_ctx (ctx_app1 C e2) G t G' t'
| typing_ctx_app : forall C G G' t t2 t' e1,
    typing G' e1 (typ_arr t2 t') ->
    typing_ctx C G t G' t2  ->
    typing_ctx (ctx_app2 e1 C) G t G' t'.

Hint Constructors typing_ctx.


(* The replacement operation preserves types *)
Lemma typing_replace : forall C G t G' t' e,
   typing_ctx C G t G' t' -> typing G e t -> typing G' (replace C e) t'.
Proof.
  intros C G t G' t' e H H1. 
  induction H; simpl; auto.
  - eapply (typing_rec_exists x);
      autorewrite with lngen; auto. apply val_abs. (* lc *) admit.
    eapply (typing_abs_exists y);
      autorewrite with lngen; eauto.
  - eapply (typing_rec_exists x);
      autorewrite with lngen; auto. admit.
    eapply (typing_abs_exists y);
      autorewrite with lngen; eauto.
  - eapply (typing_rec_exists x G' _ _ _ t');
    autorewrite with lngen; auto. admit.
    eapply (typing_abs_exists y);
      autorewrite with lngen; eauto.
  - eapply (typing_abs_exists x);
      autorewrite with lngen; eauto.
  - eapply typing_app; eauto.
  - eapply typing_app; eauto.
Admitted.

(* Lemma 46.1 *)
Lemma extension : forall G G' t t' C, typing_ctx C G t G' t' ->
                                 exists G'', G = G'' ++ G'.
Proof.
  intros. induction H; auto.
  - exists nil. simpl. auto.
  - destruct IHtyping_ctx as [G'' EQ].
    exists (G'' ++ (y ~ t') ++ (x ~ typ_nat)).
    simpl_env. auto.
  - destruct IHtyping_ctx as [G'' EQ].
    exists (G'' ++ (x ~ t1)).
    simpl_env. auto.
Qed.


(* Definition 46.4 *)

Definition kleene_equivalence e1 e2 :=
  exists v, value v /\ multistep e1 v /\ multistep e2 v.

(* NOTE: Bob claims that this relation is clearly reflexive. But we can't 
   prove that yet. *)

Lemma kleene_sym  : forall e1 e2, kleene_equivalence e1 e2 -> kleene_equivalence e2 e1.
Proof.
  unfold kleene_equivalence.
  intros.  destruct H as [v [V [M1 M2]]].
  exists v. auto.
Qed.

Lemma kleene_trans : forall e1 e2 e3, kleene_equivalence e1 e2 -> kleene_equivalence e2 e3
                                 -> kleene_equivalence e1 e3.
Proof.
  unfold kleene_equivalence.
  intros.  destruct H as [v [V [M1 M2]]]. destruct H0 as [v' [V' [M1' M2']]].
  exists v. split. auto. admit. (* derterminancy of evaluation *)
Admitted.


Definition observational_equivalence G e e' t :=
  typing G e  t /\ typing G e' t /\
  forall C, 
    typing_ctx C G t nil typ_nat ->
    kleene_equivalence (replace C e) (replace C e').

(* We want to prove 46.6, but first we need a general definition of 
   a "consistent congruence relation" *)

Record open_equivalence (R : env -> exp -> exp -> typ -> Prop) := mkO
{
  (* Only holds for well-typed terms (with the same type) *)
  open_typed : forall G e1 e2 t , R G e1 e2 t -> typing G e1 t /\ typing G e2 t;

  (* Is an equivalence relation *)
  open_refl : forall G e t, typing G e t -> R G e e t;
  open_sym  : forall G e1 e2 t, R G e1 e2 t -> R G e2 e1 t;
  open_trans : forall G e1 e2 e3 t, R G e1 e2 t -> R G e2 e3 t -> R G e1 e3 t;

  (* Is consistent *)
  open_consistent :  forall e1 e2,
      R nil e1 e2 typ_nat -> kleene_equivalence e1 e2;

  (* Is a congruence *)
  open_congruence : forall G e e' t,
      R G e e' t -> forall C G' t', typing_ctx C G t G' t'
                              -> R G' (replace C e) (replace C e') t'
}.

(* Lemma 46.6 (first part). *)
Lemma open_observational_notyet : open_equivalence observational_equivalence.
Admitted.
(* We can't actually prove this yet, because it relies on the 
reflexivity of kleene_equivalence. *)

(* However, we can prove everything else. *)
Lemma  observational_typed :
  forall G e1 e2 t , observational_equivalence G e1 e2 t -> typing G e1 t /\ typing G e2 t.
Proof.
  intros.  destruct H as [T1 [T2 CTX]]. auto.
Qed.
  
  (* Is an equivalence relation *)
Lemma observational_sym  : forall G e1 e2 t, observational_equivalence G e1 e2 t -> observational_equivalence G e2 e1 t.
Proof.
  unfold observational_equivalence.
  intros. destruct H as [T1 [T2 CTX]].
  repeat split; auto.
  intros C CC.
  apply kleene_sym. auto.
Qed.

Lemma observational_trans :
  forall G e1 e2 e3 t, observational_equivalence G e1 e2 t
                  -> observational_equivalence G e2 e3 t
                  -> observational_equivalence G e1 e3 t.
Proof.  
  unfold observational_equivalence.
  intros.
  destruct H as [T1 [T2 CTX]].
  destruct H0 as [T1' [T2' CTX']].
  repeat split; auto.
  intros C CC.
  apply kleene_trans with (e2 := replace C e2). auto. auto.
Qed.
  
  
 (* Is consistent *)
Lemma  observational_consistent :  forall e1 e2,
    observational_equivalence nil e1 e2 typ_nat -> kleene_equivalence e1 e2.
Proof.
  unfold observational_equivalence.
  intros.
  destruct H as [T1 [T2 CTX]].
  apply CTX with (C := ctx_top).
  eapply typing_ctx_top.
Qed.

Fixpoint compose (C1 : ctx) (C2 : ctx) : ctx :=
  match C1 with
  | ctx_top => C2
  | ctx_s C => ctx_s (compose C C2)
  | ctx_rec1 C e1 x y t e2 => ctx_rec1 (compose C C2) e1 x y t e2
  | ctx_rec2 e0 C x y t e2 => ctx_rec2 e0 (compose C C2) x y t e2
  | ctx_rec3 e0 e1 x y t C => ctx_rec3 e0 e1 x y t (compose C C2)
  | ctx_abs t x C => ctx_abs t x (compose C C2)
  | ctx_app1 C e2 => ctx_app1 (compose C C2) e2
  | ctx_app2 e1 C => ctx_app2 e1 (compose C C2)
  end.

Lemma replace_compose : forall C1 C2 e, replace C1 (replace C2 e) = replace (compose C1 C2) e.
Proof.
  intros C1. induction C1; intros; simpl; try rewrite IHC1; auto.
Qed.

(* Lemma 46.2 *)
Lemma typing_compose : forall C1 C2 G t G' t' G'' t'',
    typing_ctx C1 G t G' t' ->
    typing_ctx C2 G' t' G'' t'' ->
    typing_ctx (compose C2 C1) G t G'' t''.
Proof.
  intros. 
  induction H0; intros; simpl; eauto.
Qed.
    
  (* Is a congruence *)
Lemma observational_congruence : forall G e e' t,
    observational_equivalence G e e' t -> forall C G' t',
      typing_ctx C G t G' t'
      -> observational_equivalence G' (replace C e) (replace C e') t'.
Proof.
  intros.
  unfold observational_equivalence.
  destruct (observational_typed _ _ _ _ H) as [T1 T2].
  repeat split. eapply typing_replace; eauto.
  eapply typing_replace; eauto.
  intros C' CT'.
  rewrite replace_compose.
  rewrite replace_compose.
  destruct H as [Te [Te' CTX]].
  eapply CTX.
  eapply typing_compose; eauto.
Qed.

(* ------------ *)

(* Lemma 46.6 *)
(* Observational equivalence is the *largest* open_equivalence *)

Lemma coarsest :
  forall R G e1 e2 t,
    open_equivalence R -> R G e1 e2 t -> observational_equivalence G e1 e2 t.
Proof.
  intros R G e1 e2 t OPEN H.
  destruct (open_typed R OPEN _ _ _ _ H).
  unfold observational_equivalence.
  split. auto.
  split. auto.
  intros C CT.
  pose (CONG := open_congruence R OPEN _ _ _ _ H C nil typ_nat CT).
  clearbody CONG.
  pose (CONS := open_consistent R OPEN _ _ CONG).
  auto.
Qed.  


(*  ----------------- closing substitutions --------------------- *)

Definition closing_subst := list (atom * exp).

Inductive typing_cs : env -> closing_subst -> Prop :=
| typing_cs_nil : typing_cs nil nil
| typing_cs_cons : forall G g x t e,
    typing nil e t ->
    typing_cs G g ->
    x `notin` dom G \u dom g ->
    typing_cs ((x ~ t) ++ G) ((x ~ e) ++ g).

Hint Constructors typing_cs.
              
Fixpoint apply_cs (g : closing_subst) (e : exp) : exp :=
  match e with
  | var_f y => match binds_lookup _ y g with
              | inl (exist _ e0 _) => e0
                    | inr _ => e
                end
  | s e1 => s (apply_cs g e1)
  | app e1 e2 => app (apply_cs g e1) (apply_cs g e2)
  | abs t e1 => abs t (apply_cs g e1)
  | rec e0 e1 e2 => rec (apply_cs g e0) (apply_cs g e1) (apply_cs g e2)
  | _ => e
  end.

  
Inductive eq_cs (R : env -> exp -> exp -> typ -> Prop) : env -> closing_subst -> closing_subst -> Prop :=
| eq_cs_nil  : eq_cs R nil nil nil
| eq_cs_cons : forall G g1 g2 x t e1 e2,
    eq_cs R G g1 g2 ->
    R nil e1 e2 t ->
    x `notin` dom g1 \u dom g2 \u dom G ->
    eq_cs R ((x ~ t) ++ G) ((x ~ e1)++ g1) ((x ~ e2) ++ g2).

Hint Constructors eq_cs.

Lemma eq_cs_typing : forall G g1 g2,
    eq_cs observational_equivalence G g1 g2 -> typing_cs G g1 /\ typing_cs G g2.
Proof.                                
  intro G. induction G; intros. inversion H. auto.
  inversion H. subst.
  destruct (observational_typed  _ _ _ _ H3).
  destruct (IHG _ _ H2).
  split. econstructor; eauto.
  econstructor; eauto.
Qed.      

(* -----   Lemma 46.7 -------  *)

Lemma apply_nil : forall e, apply_cs nil e = e.
Proof.
  induction e; simpl; try rewrite IHe; auto.
  rewrite IHe1. rewrite IHe2. rewrite IHe3. auto.
  rewrite IHe1. rewrite IHe2. auto.
Qed.  

Lemma apply_cons : forall x e1 g e,
    x `notin` dom g -> apply_cs ((x ~ e1) ++ g) e = apply_cs g (subst_exp e1 x e).
Proof.
  intros.
  induction e; simpl; auto.
  - destruct (KeySetFacts.eq_dec x0 x).
    + subst.
      destruct (binds_lookup exp x g). destruct s.
      apply binds_In in b. contradiction.
      simpl. admit.
    + destruct (binds_lookup exp x0 g). destruct s.
      admit.
      simpl. destruct (x0 == x). contradiction. admit.
  - simpl in IHe. rewrite IHe. auto.
  - simpl in *. rewrite IHe1. rewrite IHe2. rewrite IHe3. auto.
Admitted.


Lemma apply_cs_typing : forall G g, typing_cs G g -> forall e t, typing G e t -> typing nil (apply_cs g e) t.
Proof.
  intros G g H. induction H.
  intros. rewrite apply_nil. auto.
  intros.
  pose (K := typing_uniq _ _ _ H2). inversion K. subst. clear K.
  rewrite apply_cons.
  apply IHtyping_cs.
  eapply typing_subst_simple. eauto.
  eapply typing_weakening with (F := G)(E:=nil) in H.
  rewrite app_nil_r in H. auto.
  rewrite app_nil_r. auto. auto.
Qed.  
  
(* Closing substitutions close terms. *)
Lemma closing_typed : forall G g, typing_cs G g -> 
    forall e e' t, observational_equivalence G e e' t -> 
    observational_equivalence nil (apply_cs g e) (apply_cs g e') t.
Proof.
  intros.  unfold observational_equivalence in *.
  destruct H0 as [T1 [T2 CT]].
  split. eapply apply_cs_typing. eauto. eauto.
  split. eapply apply_cs_typing. eauto. eauto.
  intros C CTX.
Admitted.

Lemma closed_context : forall C g t,
    typing_ctx C nil t nil typ_nat -> forall G, typing_cs G g ->
    forall e, replace C (apply_cs g e) = apply_cs g (replace C e).
Proof.
  intros C. induction C; intros;  simpl; auto.
  - inversion H.
    erewrite IHC; eauto.
  - inversion H.
    erewrite IHC; eauto.
    admit.
Admitted.

(*
Fixpoint make_ctx (G : env)(g : closing_subst)(C : ctx) : ctx :=
  match G with
  | nil => ctx_top
  | cons (x,t) G' => ctx_abs t x (make_ctx G' g (ctx_app1 C (apply_cs g (var_f x))))
  end.

Lemma typing_make_ctx :
  forall G g, typing_ctx C G t G typ_nat ->
         typing_ctx (make_ctx G g C) G t nil typ_nat
*)

Lemma closing_eq : forall G e e' t g g',
    observational_equivalence G e e' t -> eq_cs observational_equivalence G g g' ->
    observational_equivalence nil (apply_cs g e) (apply_cs g' e') t.
Proof.
  intros.
  unfold observational_equivalence.
  destruct (observational_typed _ _ _ _ H) as [h0 h1].
  destruct (eq_cs_typing _ _ _ H0) as [Tg Tg'].
  split. apply apply_cs_typing with (G := G); eauto. 
  split. apply apply_cs_typing with (G := G); eauto. 
  intros C CT.
  rewrite closed_context with (t := t)(G := G); auto.
  rewrite closed_context with (t := t)(G := G); auto.
Admitted.

(* --------------------- 46.2 Logical equivalence -------------------------- *)

Fixpoint logical_equivalence (e e' : exp) (t : typ) {struct t} : Prop :=
  match t with
  | typ_nat => typing nil e typ_nat /\ typing nil e' typ_nat /\ kleene_equivalence e e' 
  | typ_arr t1 t2 =>
    typing nil e (typ_arr t1 t2) /\ typing nil e' (typ_arr t1 t2) /\
    forall e1 e1', logical_equivalence e1 e1' t1 ->
              logical_equivalence (app e e1) (app e' e1') t2
  end.


(* ------------------ proof by nat-induction --------------------- *)

Fixpoint from_nat (n : nat) : exp :=
  match n with
  | O => z
  | S n => s (from_nat n)
  end.

Inductive as_nat : nat -> exp -> Prop :=
| as_nat_z : as_nat O z
| as_nat_s : forall n e, as_nat n e -> as_nat (S n) (s e).
Hint Constructors as_nat.

Lemma to_nat : forall e, value e -> typing nil e typ_nat -> exists n, as_nat n e.
Proof. 
  intros e V. induction V; intros.
  inversion H. exists O. auto.
  inversion H.
  destruct (IHV H2) as [m A].
  exists (S m). auto.
  inversion H0.
Qed.

Lemma as_from_nat : forall n, as_nat n (from_nat n).
Proof. induction n.
       simpl. auto.
       simpl in *. auto.
Qed.

Lemma nat_induction : forall e e', logical_equivalence e e' typ_nat
                              -> forall (R : exp -> exp -> Prop), R z z -> (forall v, value v -> R v v -> R (s v) (s v)) -> R e e'.
Proof.                                  
  intros.
  unfold logical_equivalence in H.
  unfold kleene_equivalence in H.
  destruct H as [T1 [T2 [v [VV [Se Se']]]]].
  destruct (to_nat v VV). admit.
  generalize dependent e. generalize dependent e'. generalize dependent v. induction x.
  - intros. inversion H. subst.  (* Need to know that R is closed under reverse_evaluation *)
    admit.
  - intros. inversion H. subst.
    assert (R (s e0) (s e0) -> R e e'). admit.
    apply H2. apply H1. inversion VV. auto.
    inversion VV.
    apply (IHx e0); eauto. admit. admit. admit. admit.
Admitted.

(* ------------------ sym & trans --------------------- *)

Lemma logical_typing : forall t e e',
    logical_equivalence e e' t -> typing nil e t /\ typing nil e' t.
Proof.
  induction t; intros; simpl in *.
  destruct H as [H1 [H2 _]]. auto.
  destruct H as [H1 [H2 G3]].
  auto.
Qed.  

(* Lemma 46.9 *)
Lemma logical_sym : forall e e' t,
    logical_equivalence e e' t -> logical_equivalence e' e t.
Admitted.

Lemma logical_trans : forall e e' e'' t,
    logical_equivalence e e' t ->
    logical_equivalence e' e'' t ->
    logical_equivalence e e'' t.
Admitted.


(* -------------- extension to open terms --------------------- *)

Definition open_logical_equivalence G e e' t :=
  typing G e t /\
  typing G e' t /\
  forall g g', eq_cs (fun G => logical_equivalence) G g g' ->
          logical_equivalence (apply_cs g e) (apply_cs g' e') t.

Lemma open_logical_sym : forall G e e' t,
    open_logical_equivalence G e e' t -> open_logical_equivalence G e' e t.
Admitted.

Lemma open_logical_trans : forall G e e' e'' t,
    open_logical_equivalence G e e' t ->
    open_logical_equivalence G e' e'' t ->
    open_logical_equivalence G e e'' t.
Admitted.

(* -------------------------- 46.3 ---------------------------- *)

Lemma converse_evaluation_logical : forall e e' t,
    logical_equivalence e e' t -> forall d, eval e e -> logical_equivalence d e' t.
Proof.
  intros e e' t. induction t.
  - intros.
    unfold logical_equivalence in *. unfold kleene_equivalence in *.
    admit.
  - intros.
    simpl in *.
    admit.
Admitted.


Lemma consistency_logical : forall e e', logical_equivalence e e' typ_nat -> kleene_equivalence e e'.
Proof.
  unfold logical_equivalence.
  intros. destruct H as [h0 [h1 h2]].
  auto.
Qed.


Lemma open_logical_refl : forall G e t, typing G e t -> open_logical_equivalence G e e t.
Proof.
  intros G e t H.
  induction H; unfold open_logical_equivalence;
    split; eauto; split; eauto; intros g g' EQ.
  - admit.
  - simpl. split. auto. split. auto.
    unfold kleene_equivalence. exists z. split. auto. split. admit. admit.
  - admit.
Admitted.

Lemma termination : forall e, typing nil e typ_nat -> exists v, multistep e v /\ value v.
Proof.
  intros e H.
  apply open_logical_refl in H.
  unfold open_logical_equivalence in H.
  destruct H as [_ [_ H0]].
  destruct (H0 nil nil) as [k0 [k1 k2]].
  apply eq_cs_nil.
  unfold kleene_equivalence in k2.
  destruct k2 as [v [VV [Ms1 Ms2]]].
  exists v. simpl in *. split. rewrite apply_nil in Ms1.  auto.
  auto.
Qed.

(* This wasn't obvious before, but it is provable now. *)
Lemma kleene_refl : forall e, typing nil e typ_nat -> kleene_equivalence e e.
Proof.
  intros e H.
  apply termination in H.
  unfold kleene_equivalence.
  destruct H as [v [MS V]].
  exists v. auto.
Qed.

Lemma open_observational : open_equivalence observational_equivalence.
  apply mkO.
  - apply observational_typed. 
  - intros. unfold observational_equivalence.
    split. auto. split. auto. intros.
    apply kleene_refl.
    apply typing_replace with (G := G) (t:=t). auto. auto.
  - apply observational_sym.
  - apply observational_trans.
  - apply observational_consistent.
  - apply observational_congruence. 
Qed.

(* Lemma 46.16 *)
Lemma open_logical_congruence :
  forall C0 G t G0 t0,
    typing_ctx C0 G t G0 t0 ->
    forall e e', open_logical_equivalence G e e' t ->
            open_logical_equivalence G0 (replace C0 e) (replace C0 e') t0.
Proof.
  intros C0 G t G0 t0 H. induction H; intros; simpl; auto.
  - unfold open_logical_equivalence in *.
    destruct H0 as [Te [Te' LL]].
    split. econstructor. eapply typing_replace; eauto.
    split. econstructor. eapply typing_replace; eauto.
    intros g g' EQ.
    simpl.
    split. econstructor. eapply apply_cs_typing with (G := G').
    admit. eapply typing_replace; eauto.  (* equal cs are typed. *)
    split. econstructor. eapply apply_cs_typing.
    admit. eapply typing_replace; eauto.
    destruct (IHtyping_ctx e e') as [k0 [k1 FF]].
    repeat split.  auto. auto. auto.
    destruct (FF g g') as [h0 [h1 GG]]. auto.
    unfold kleene_equivalence in *.
    destruct GG as [v [MS1 MS2]].
    exists (s v). split. auto.
    split. admit. admit. (* multistep is a congruence *)
Admitted.
    
Lemma open_logical : open_equivalence open_logical_equivalence.
Proof.
  apply mkO.
  - intros. unfold open_logical_equivalence in H.
    destruct H as [T1 [T2 _]]. auto.
  - apply open_logical_refl.
  - apply open_logical_sym.
  - apply open_logical_trans.
  - (* consistent *) intros.
    destruct H as [T1 [T2 C]].
    destruct (C nil nil) as [h0 [h1 k]]. eauto.
    rewrite apply_nil in k.
    rewrite apply_nil in k.
    auto.
  - (* congruent *)
    intros.
    eapply open_logical_congruence; eauto.
Qed.

(* Theorem 46.17 *)
(* Logical equivalence implies observational equivalence. *)
Lemma logical_is_observational : forall G e e' t,
    open_logical_equivalence G e e' t ->
    observational_equivalence G e e' t.
Proof.
  intros.
  eapply coarsest.
  eapply open_logical. auto.
Qed.

(* Lemma 46.19 *)
Lemma closed_observational_is_logical : forall t e e', 
    observational_equivalence nil e e' t -> logical_equivalence e e' t.
Proof.
  induction t.
  - intros. unfold logical_equivalence, observational_equivalence in *.
    destruct H as [T1 [T2 CT]].
    split. auto. split. auto.
    pose (K := CT ctx_top (@typing_ctx_top nil typ_nat)).
    simpl in K. auto.
  - intros.
    pose (M := H).
    destruct M as [T1 [T2 CT]].
    split. auto. split. auto.
    intros e1 e1' Le1.
    destruct (logical_typing _ _ _ Le1) as [U1 U2].
    assert (observational_equivalence nil e1 e1' t1).
    { eapply logical_is_observational.
      unfold open_logical_equivalence.
      split. auto. split. auto.
      intros. inversion H0. subst.
      rewrite apply_nil.
      rewrite apply_nil.
      auto. }
    assert (observational_equivalence nil (app e e1) (app e' e1') t2).
    { eapply observational_trans with (e2 := app e e1').
      replace (app e e1) with (replace (ctx_app2 e ctx_top) e1); auto.
      replace (app e e1') with (replace (ctx_app2 e ctx_top) e1'); auto.
      eapply observational_congruence. eauto.
      eauto.
      replace (app e e1') with (replace (ctx_app1 ctx_top e1') e); auto.
      replace (app e' e1') with (replace (ctx_app1 ctx_top e1') e'); auto.
      eapply observational_congruence. eauto.
      eauto. }
    eauto.
Qed.    
    
(* Lemma 46.19 *)
Lemma observational_is_logical : forall G e e' t, 
    observational_equivalence G e e' t -> open_logical_equivalence G e e' t.
Proof.
  intros.
  unfold open_logical_equivalence.
  destruct (observational_typed _ _ _ _ H) as [T1 T2].
  split. auto.
  split. auto.
  intros g g' EQg.
  apply closed_observational_is_logical.
  apply closing_eq with (G := G). auto.
  admit. (* map Lemma 46.19 *)
Admitted.