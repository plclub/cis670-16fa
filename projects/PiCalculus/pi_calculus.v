Require Import Coq.Relations.Relation_Operators.
Require Import Metalib.Metatheory.

Module Syntax.

Inductive channel : Set :=
| free : atom -> channel
| bound : nat -> channel
.
  
Inductive process : Set :=
| stop : process 
| input : channel -> process -> process
| output : channel -> channel -> process -> process
| compose : process -> process -> process
| replicate : process -> process.

Definition fv_channel c :=
  match c with
    | free f => singleton f
    | bound _ => empty
  end.

Fixpoint fv p :=
  match p with
    | stop => empty
    | input c1 p => union (fv p) (fv_channel c1)
    | output c1 c2 p => union (fv p) (union (fv_channel c1) (fv_channel c2))
    | compose p1 p2 => union (fv p1) (fv p2) 
    | replicate p => fv p
  end.

Definition open_channel n a c :=
  match c with
    | free f => free f
    | bound b => if beq_nat b n then a else bound b
  end.

Fixpoint open_rec n a p :=
  match p with
    | stop => stop
    | input c p =>
      input (open_channel n a c) (open_rec (S n) a p)
    | output c1 c2 p =>
      output (open_channel n a c1) (open_channel n a c2) (open_rec n a p)
    | replicate p => replicate (open_rec n a p)
    | compose p1 p2 => compose (open_rec n a p1) (open_rec n a p2)
  end.

Definition open a p := open_rec 0 a p.

Inductive lc_channel : channel -> Prop :=
| lc_free : forall a, lc_channel (free a)
.

(* This is different from local closure of expressions in e.g. System T,
since we don't actually care if when we substitute, the name is free
in the expression we're substituting for.
*)
Inductive lc : process -> Prop :=
| lc_replicate : forall p, lc p -> lc (replicate p)
| lc_compose : forall p1 p2, lc p1 -> lc p2 -> lc (compose p1 p2)
| lc_stop : lc stop
| lc_output : forall c1 c2 p, lc p -> lc_channel c1 -> lc_channel c2 -> lc (output c1 c2 p)
| lc_input : forall c p, lc_channel c -> lc p -> lc (input c p)
.
                                                  
End Syntax.

Module Semantics.

Import Syntax.

Inductive context : Type :=
| c_input : channel -> channel -> context -> context
| c_output : channel -> channel -> context -> context
| c_replicate : context -> context
| c_compose_l : context -> process -> context
| c_compose_r : process -> context -> context
| c_hole : context
.

Fixpoint fill (c : context) (p : process) : process :=
  match c with
    | c_input c1 c2 con => input c1 (fill con p)
    | c_output c1 c2 con => output c1 c2 (fill con p)
    | c_hole => p
    | c_replicate con => replicate (fill con p)
    | c_compose_l con r => compose (fill con p) r
    | c_compose_r l con => compose l (fill con p)
  end.

Inductive congruent : process -> process -> Prop :=
| cong_compose_comm : forall P1 P2, congruent (compose P1 P2) (compose P2 P1)
| cong_compose_assoc : forall P1 P2 P3, congruent (compose P1 (compose P2 P3)) (compose (compose P1 P2) P3)
| cong_zero : forall P, congruent (compose P stop) P
| cong_replicate : forall P, congruent (replicate P) (compose P (replicate P))
| cong_context : forall c P Q, congruent P Q -> congruent (fill c P) (fill c Q)
| cong_refl : forall P, congruent P P
| cong_symm : forall P Q, congruent P Q -> congruent Q P
| cong_trans : forall P Q R, congruent P Q -> congruent Q R -> congruent P R
.

(*Definition congruent : process -> process -> Prop :=
  clos_refl_sym_trans process cong_base.*)

Inductive step_process_base : process -> process -> Prop :=
| step_composition : forall P1 P2 P3, step_process_base P1 P2 -> step_process_base (compose P1 P3) (compose P2 P3)
| step_communication : forall c z P Q, step_process_base (compose (output c z Q) (input c P)) (compose Q (open z P)).

Definition step_process P Q : Prop :=
  exists P' Q', congruent P P' /\ congruent Q Q' /\ step_process_base P' Q'.

Inductive step_process_cong : process -> process -> Prop :=
| step_composition_cong : forall P1 P2 P3, step_process_cong P1 P2 -> step_process_cong (compose P1 P3) (compose P2 P3)
| step_communication_cong : forall c z P Q, step_process_cong (compose (output c z Q) (input c P)) (compose Q (open z P))
| step_cong : forall P Q P' Q', step_process_cong P Q -> congruent P P' -> congruent Q Q' -> step_process_cong P' Q'.

Theorem cong_end : forall P Q, step_process_cong P Q <-> step_process P Q.
Proof.
  intros. split.
  - intros. induction H.
    + unfold step_process. destruct IHstep_process_cong as [P1'].
      destruct H0 as [P2'].
      exists (compose P1' P3). exists (compose P2' P3).
      destruct H0 as [CP1 H0]. destruct H0 as [CP2 SPB].
      repeat split.
      * assert (compose P1 P3 = fill (c_compose_l c_hole P3) P1); eauto.
        assert (compose P1' P3 = fill (c_compose_l c_hole P3) P1'); eauto.
        rewrite H0; rewrite H1. eapply cong_context. eapply CP1.
      * assert (compose P2 P3 = fill (c_compose_l c_hole P3) P2); eauto.
        assert (compose P2' P3 = fill (c_compose_l c_hole P3) P2'); eauto.
        rewrite H0; rewrite H1. eapply cong_context. eapply CP2.
      * constructor. eapply SPB.
    + unfold step_process.
      exists (compose (output c z Q) (input c P)).
      exists (compose Q (open z P)).
      repeat split; try (eapply cong_refl); constructor.
    + destruct IHstep_process_cong as [P1].
      destruct H2 as [Q1]. exists P1. exists Q1.
      repeat split.
      * eapply cong_trans. eapply cong_symm; eauto. eapply H2. 
      * eapply cong_trans. eapply cong_symm; eauto. eapply H2. 
      * eapply H2.
  - intros. destruct H as [P']. destruct H as [Q'].
    destruct H as [CPP' H]. destruct H as [CQQ' H].
    apply step_cong with (P := P') (Q := Q').
    generalize dependent P. generalize dependent Q. induction H.
    + intros. eapply step_composition_cong. eapply IHstep_process_base.
      eapply cong_refl. eapply cong_refl.
    + intros. eapply step_communication_cong.
    + eapply cong_symm; eauto.
    + eapply cong_symm; eauto.
Qed.

Inductive label :=
| send_label : channel -> channel -> label
| recv_label : channel -> channel -> label
| tau_label : label.

Definition fv_label l :=
  match l with
    | send_label c1 c2 => union (fv_channel c1) (fv_channel c2) 
    | recv_label c1 c2 => union (fv_channel c1) (fv_channel c2)
    | tau_label => empty
  end.

Definition bound_label l :=
  match l with
    | recv_label c1 c2 => fv_channel c2
    | _ => empty
  end.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let D := gather_atoms_with (fun x : process => fv x) in
  constr:(A `union` B `union` D).

Inductive lts : process -> label -> process -> Prop :=
| lts_comp_left : forall P P' Q l, lts P l P' -> lts (compose P Q) l (compose P' Q)
| lts_comp_right : forall P Q Q' l, lts Q l Q' -> lts (compose P Q) l (compose P Q')
| lts_input : forall P c n, lts (input c P) (recv_label c n) (open n P)
| lts_output : forall P c c', lts (output c c' P) (send_label c c') P
| lts_comm_left : forall P P' Q Q' c n, lts P (send_label c n) P' -> lts Q (recv_label c n) Q' -> lts (compose P Q) (tau_label) (compose P' Q')
| lts_comm_right : forall P P' Q Q' c n, lts P (recv_label c n) P' -> lts Q (send_label c n) Q' -> lts (compose P Q) tau_label (compose P' Q')
| lts_rep_act : forall P a P', lts P a P' -> lts (replicate P) a (compose P' (replicate P))
| lts_rep_comm : forall P c n P' P'',
                   lts P (send_label c n) P' -> lts P (recv_label c n) P'' ->
                   lts (replicate P) tau_label (compose (compose P' P'') (replicate P))
.

Lemma lts_input_helper :
  forall P Q c1 c2, lts P (recv_label c1 c2) Q ->
                exists R S, congruent P (compose (input c1 R) S) /\
                            congruent Q (compose (open c2 R) S).
Proof.
  intros. remember (recv_label c1 c2). induction H; try (inversion Heql; subst).
  - apply IHlts in H0. destruct H0 as [R]. destruct H0 as [S].
    exists R. exists (compose S Q).
    split.
    + apply cong_trans with (Q := (compose (compose (input c1 R) S) Q)).
      assert (compose P Q = fill (c_compose_l c_hole Q) P); eauto.
      assert (compose (compose (input c1 R) S) Q = fill (c_compose_l c_hole Q) (compose (input c1 R) S)); eauto.
      rewrite H1; rewrite H2; eapply cong_context. eapply H0.
      eapply cong_symm; eapply cong_compose_assoc.
    + apply cong_trans with (Q := (compose (compose (open c2 R) S) Q)).
      assert (compose P' Q = fill (c_compose_l c_hole Q) P'); eauto.
      assert (compose (compose (open c2 R) S) Q = fill (c_compose_l c_hole Q) (compose (open c2 R) S)); eauto.
      rewrite H1; rewrite H2; eapply cong_context. eapply H0.
      eapply cong_symm; eapply cong_compose_assoc.
  - apply IHlts in H0. destruct H0 as [R]. destruct H0 as [S].
    exists R. exists (compose P S).
    split.
    + eapply cong_trans with (Q := (compose P (compose (input c1 R) S))).
      assert (compose P Q = fill (c_compose_r P c_hole) Q); eauto.
      assert (compose P (compose (input c1 R) S) = fill (c_compose_r P c_hole) (compose (input c1 R) S)); eauto.
      rewrite H1; rewrite H2; eapply cong_context. eapply H0.
      eapply cong_trans. eapply cong_compose_assoc.
      eapply cong_trans with (Q := (compose (compose (input c1 R) P) S)).
      assert (compose (compose P (input c1 R)) S = fill (c_compose_l c_hole S) (compose P (input c1 R))); eauto.
      assert (compose (compose (input c1 R) P) S = fill (c_compose_l c_hole S) (compose (input c1 R) P)); eauto.
      rewrite H1; rewrite H2; eapply cong_context.
      eapply cong_compose_comm. eapply cong_symm; eapply cong_compose_assoc.
    + apply cong_trans with (Q := (compose P (compose (open c2 R) S))).
      assert (compose P Q' = fill (c_compose_r P c_hole) Q'); eauto.
      assert (compose P (compose (open c2 R) S) = fill (c_compose_r P c_hole) (compose (open c2 R) S)); eauto.
      rewrite H1; rewrite H2; eapply cong_context; eapply H0.
      eapply cong_trans. eapply cong_compose_assoc.
      eapply cong_trans.
      assert (compose (compose P (open c2 R)) S = fill (c_compose_l c_hole S) (compose P (open c2 R))); eauto.
      rewrite H1; eapply cong_context. eapply cong_compose_comm. simpl.
      eapply cong_symm; eapply cong_compose_assoc.
  - inversion Heql; subst. exists P. exists stop.
    split. eapply cong_symm; eapply cong_zero. eapply cong_symm; eapply cong_zero.
  - eapply IHlts in H0. destruct H0 as [R]. destruct H0 as [S].
    exists R. exists (compose S (replicate P)). split.
    + eapply cong_trans. eapply cong_replicate.
      eapply cong_trans.
      assert (compose P (replicate P) = fill (c_compose_l c_hole (replicate P)) P); eauto.
      rewrite H1. eapply cong_context. eapply H0. simpl.
      eapply cong_symm. eapply cong_compose_assoc.
    + eapply cong_trans.
      assert (compose P' (replicate P) = fill (c_compose_l c_hole (replicate P)) P'); eauto.
      rewrite H1; eapply cong_context. eapply H0. simpl.
      eapply cong_symm; eapply cong_compose_assoc.
Qed.

Lemma lts_output_helper :
  forall P Q c1 c2, lts P (send_label c1 c2) Q ->
                    exists R S, congruent P (compose (output c1 c2 R) S) /\
                                congruent Q (compose R S).
Proof.
  intros. remember (send_label c1 c2). induction H; try (inversion Heql; subst).
  - apply IHlts in H0. destruct H0 as [R]. destruct H0 as [S].
    exists R. exists (compose S Q).
    split.
    + eapply cong_trans.
      assert (compose P Q = fill (c_compose_l c_hole Q) P); eauto.
      rewrite H1. eapply cong_context. eapply H0. simpl.
      eapply cong_symm; eapply cong_compose_assoc.
    + eapply cong_trans.
      assert (compose P' Q = fill (c_compose_l c_hole Q) P'); eauto.
      rewrite H1. eapply cong_context. eapply H0. simpl.
      eapply cong_symm; eapply cong_compose_assoc.
  - apply IHlts in H0. destruct H0 as [R]. destruct H0 as [S].
    exists R. exists (compose P S).
    split.
    + eapply cong_trans.
      assert (compose P Q = fill (c_compose_r P c_hole) Q); eauto.
      rewrite H1; eapply cong_context. eapply H0. simpl.
      eapply cong_trans. eapply cong_compose_assoc.
      eapply cong_trans.
      assert (compose (compose P (output c1 c2 R)) S = fill (c_compose_l c_hole S) (compose P (output c1 c2 R))); eauto.
      rewrite H1; eapply cong_context. eapply cong_compose_comm. simpl.
      eapply cong_symm; eapply cong_compose_assoc.
    + eapply cong_trans.
      assert (compose P Q' = fill (c_compose_r P c_hole) Q'); eauto.
      rewrite H1; eapply cong_context. eapply H0. simpl.
      eapply cong_trans. eapply cong_compose_assoc.
      eapply cong_trans.
      assert (compose (compose P R) S = fill (c_compose_l c_hole S) (compose P R)); eauto.
      rewrite H1; eapply cong_context. eapply cong_compose_comm. simpl.
      eapply cong_symm; eapply cong_compose_assoc.
  - exists P. exists stop. split. eapply cong_symm; eapply cong_zero.
    eapply cong_symm; eapply cong_zero.
  - eapply IHlts in H0. destruct H0 as [R]. destruct H0 as [S].
    exists R. exists (compose S (replicate P)). split.
    + eapply cong_trans. eapply cong_replicate.
      eapply cong_trans.
      assert (compose P (replicate P) = fill (c_compose_l c_hole (replicate P)) P); eauto.
      rewrite H1; eapply cong_context. apply H0. simpl.
      eapply cong_symm; eapply cong_compose_assoc.
    + eapply cong_trans.
      assert (compose P' (replicate P) = fill (c_compose_l c_hole (replicate P)) P'); eauto.
      rewrite H1; eapply cong_context. apply H0. simpl.
      eapply cong_symm; eapply cong_compose_assoc.
Qed.

Definition lts_cong P a Q :=
  exists P' Q', congruent P P' /\ congruent Q Q' /\ lts P' a Q'.

Theorem lts_tau_step : forall P Q, step_process P Q -> lts_cong P tau_label Q.
Proof.
  intros. destruct H as [P']. destruct H as [Q'].
  destruct H as [CPP' H]; destruct H as [CQQ' S].
  unfold lts_cong. exists P'. exists Q'. repeat split; eauto.
  clear CPP'; clear CQQ'.
  induction S.
  - eapply lts_comp_left. eapply IHS.
  - eapply lts_comm_left. constructor. constructor.
Qed.

Theorem tau_lts_comm_step : 
  forall P Q P' Q' c n, lts P (send_label c n) P' ->
                        lts Q (recv_label c n) Q' ->
                        step_process (compose P Q) (compose P' Q').
Proof.
  intros.
  eapply lts_input_helper in H0.
  eapply lts_output_helper in H.
  destruct H as [R]. destruct H as [S]. destruct H.
  destruct H0 as [R']. destruct H0 as [S']. destruct H0.
  unfold step_process.
  exists (compose (compose (output c n R) (input c R')) (compose S S')).
  exists (compose (compose R (open n R')) (compose S S')).
  repeat split.
  + eapply cong_trans. assert (compose P Q = fill (c_compose_l c_hole Q) P); eauto. rewrite H3.
    eapply cong_context. eapply H. simpl.
    eapply cong_trans. assert (compose (compose (output c n R) S) Q = fill (c_compose_r (compose (output c n R) S) c_hole) Q); eauto.
    rewrite H3. eapply cong_context. eapply H0. simpl.
    eapply cong_trans. eapply cong_symm. eapply cong_compose_assoc.
    eapply cong_trans.
    assert (compose (output c n R) (compose S (compose (input c R') S')) = fill (c_compose_r (output c n R) c_hole) (compose S (compose (input c R') S'))); eauto.
    rewrite H3. eapply cong_context. eapply cong_compose_assoc. simpl.
    eapply cong_trans.
    assert (compose (output c n R) (compose (compose S (input c R')) S') = fill (c_compose_r (output c n R) (c_compose_l c_hole S')) (compose S (input c R'))); eauto.
    rewrite H3. eapply cong_context. eapply cong_compose_comm. simpl.
    eapply cong_trans.
    assert (compose (output c n R) (compose (compose (input c R') S) S') = fill (c_compose_r (output c n R) c_hole) (compose (compose (input c R') S) S')); eauto.
    rewrite H3; eapply cong_context. eapply cong_symm; eapply cong_compose_assoc. simpl.
    eapply cong_compose_assoc.
  + eapply cong_trans. assert (compose P' Q' = fill (c_compose_l c_hole Q') P'); eauto. rewrite H3.
    eapply cong_context. eapply H1. simpl.
    eapply cong_trans. assert (compose (compose R S) Q' = fill (c_compose_r (compose R S) c_hole) Q'); eauto.
    rewrite H3. eapply cong_context. eapply H2. simpl.
    eapply cong_trans. eapply cong_symm. eapply cong_compose_assoc.
    eapply cong_trans.
    assert (compose R (compose S (compose (open n R') S')) = fill (c_compose_r R c_hole) (compose S (compose (open n R') S'))); eauto.
    rewrite H3. eapply cong_context. eapply cong_compose_assoc. simpl.
    eapply cong_trans.
    assert (compose R (compose (compose S (open n R')) S') = fill (c_compose_r R (c_compose_l c_hole S')) (compose S (open n R'))); eauto.
    rewrite H3. eapply cong_context. eapply cong_compose_comm. simpl.
    eapply cong_trans.
    assert (compose R (compose (compose (open n R') S) S') = fill (c_compose_r R c_hole) (compose (compose (open n R') S) S')); eauto.
    rewrite H3; eapply cong_context. eapply cong_symm; eapply cong_compose_assoc. simpl.
    eapply cong_compose_assoc.
  + constructor. constructor.
Qed.

Theorem tau_lts_step : forall P Q, lts P tau_label Q -> step_process P Q.
Proof.
  intros. remember tau_label. induction H; inversion Heql; subst.
  - unfold step_process. eapply IHlts in H0. destruct H0 as [P0'].
    destruct H0 as [Q']. exists (compose P0' Q). exists (compose Q' Q).
    repeat split.
    + assert (compose P Q = fill (c_compose_l c_hole Q) P); eauto.
      assert (compose P0' Q = fill (c_compose_l c_hole Q) P0'); eauto.
      rewrite H1. rewrite H2. eapply cong_context. eapply H0.
    + assert (compose P' Q = fill (c_compose_l c_hole Q) P'); eauto.
      assert (compose Q' Q = fill (c_compose_l c_hole Q) Q'); eauto.
      rewrite H1. rewrite H2. eapply cong_context.  eapply H0.
    + eapply step_composition. eapply H0.
  - unfold step_process. eapply IHlts in H0. destruct H0 as [X].
    destruct H0 as [Y]. exists (compose X P).  exists (compose Y P).
    repeat split.
    + eapply cong_trans. apply cong_compose_comm.
      assert (compose Q P = fill (c_compose_l c_hole P) Q); eauto.
      assert (compose X P = fill (c_compose_l c_hole P) X); eauto.
      rewrite H1. rewrite H2. eapply cong_context. eapply H0.
    + eapply cong_trans. apply cong_compose_comm.
      assert (compose Q' P = fill (c_compose_l c_hole P) Q'); eauto.
      assert (compose Y P = fill (c_compose_l c_hole P) Y); eauto.
      rewrite H1. rewrite H2. eapply cong_context. eapply H0.
    + eapply step_composition. eapply H0.
  - eapply tau_lts_comm_step. eapply H. eapply H0. 
  - eapply tau_lts_comm_step in H. destruct H as [P0]. destruct H as [Q0]. 
    exists P0. exists Q0.
    repeat split; eauto.
    + eapply cong_trans. eapply cong_compose_comm. eapply H. 
    + eapply cong_trans. eapply cong_compose_comm. eapply H. 
    + eapply H.
    + eauto.
  - eapply IHlts in H0. unfold step_process in *. clear IHlts.
    destruct H0 as [P'0]. destruct H0 as [Q].
    exists (compose P'0 (replicate P)). exists (compose Q (replicate P)).
    repeat split.
    + eapply cong_trans. eapply cong_replicate.
      assert (compose P (replicate P) = fill (c_compose_l c_hole (replicate P)) P); eauto. rewrite H1. eapply cong_trans. eapply cong_context.
      eapply H0. simpl. eapply cong_refl.
    + assert (compose P' (replicate P) = fill (c_compose_l c_hole (replicate P)) P'); eauto. rewrite H1. eapply cong_trans. eapply cong_context.
      eapply H0. simpl. eapply cong_refl.
    + eapply step_composition. eapply H0.
  - eapply tau_lts_comm_step in H; eauto.
    destruct H as [P0]. destruct H as [P0'].
    unfold step_process. exists (compose P0 (replicate P)).
    exists (compose P0' (replicate P)).
    repeat split.
    + eapply cong_trans. eapply cong_replicate.
      eapply cong_trans. assert (compose P (replicate P) = fill (c_compose_r P c_hole) (replicate P)); eauto.
      rewrite H1; eapply cong_context. eapply cong_replicate. simpl.
      eapply cong_trans. eapply cong_compose_assoc.
      eapply cong_trans. assert (compose (compose P P) (replicate P) = fill (c_compose_l c_hole (replicate P)) (compose P P)); eauto.
      rewrite H1; eapply cong_context. eapply H. simpl; eapply cong_refl.
    + assert (compose (compose P' P'') (replicate P) = fill (c_compose_l c_hole (replicate P)) (compose P' P'')); eauto.
      eapply cong_trans. rewrite H1; eapply cong_context. eapply H.
      simpl. eapply cong_refl.
    + eapply step_composition. eapply H.
Qed.

End Semantics.

Module EarlyBisim.

Import Syntax.
Import Semantics.

Definition early_bisimulation (R : process -> process -> Prop) :=
  (forall P1 P2, R P1 P2 -> R P2 P1) /\
  forall P1 P1' P2 l, R P1 P2 ->
                      lts P1 l P1' ->
                      exists P2', lts P2 l P2' /\ R P1' P2'.

Definition early_bisimilar (p : process) (q : process) :=
  exists R, early_bisimulation R /\ R p q.

Theorem early_bisimilarity_symm :
  forall p q, early_bisimilar p q -> early_bisimilar q p.
Proof.
  intros. destruct H as [R]. destruct H.
  unfold early_bisimilar. exists R.
  split. eauto.
  unfold early_bisimulation in H.
  destruct H. apply H. apply H0.
Qed.

Theorem early_bisimilarity_refl :
  forall p, early_bisimilar p p.
Proof.
  intros. unfold early_bisimilar.
  exists (fun p q => p = q). split; eauto.
  unfold early_bisimulation. split; eauto.
  intros; subst; eauto.
Qed.

Theorem early_bisimilarity_trans :
  forall p q r, early_bisimilar p q -> early_bisimilar q r -> early_bisimilar p r.
Proof.
  intros. unfold early_bisimilar in *. destruct H as [R1]; destruct H0 as [R2].
  destruct H; destruct H0.
  exists (clos_trans process (fun p q => (R1 p q \/ R2 p q))).
  split.
  - unfold early_bisimulation in *. split.
    + intros. induction H3. destruct H3. eapply t_step.
      left; apply H; eauto.
      eapply t_step. right; apply H0; eauto.
      eapply t_trans. eapply IHclos_trans2. eapply IHclos_trans1.
    + intros. generalize dependent P1'. induction H3.
      * destruct H3. destruct H. intros. eapply H4 in H5. destruct H5.
        exists x0. split. destruct H5. apply H5. eapply t_step. destruct H5. left; apply H6. apply H3.
        intros. eapply H0 in H4. destruct H4. destruct H4.
        exists x0. split. apply H4. eapply t_step. right; apply H5. apply H3.
      * intros. apply IHclos_trans1 in H4. destruct H4. destruct H3.
        apply IHclos_trans2 in H3. destruct H3. destruct H3.
        exists x1. split. apply H3. eapply t_trans. apply H4. apply H5.
  - eapply t_trans. eapply t_step. left; apply H1.
    eapply t_step. right; apply H2.
Qed.

End EarlyBisim.

Module Relations.

Import Syntax.
Import Semantics.

Definition relation := process -> process -> Prop.
Definition symmetric (R : relation) := forall P Q, R P Q -> R Q P.
Definition subset (R : relation) (S : relation) := forall P Q, R P Q -> S P Q.
Definition reverse (R : relation) := fun P Q => R Q P.
Definition r_compose (R : relation) (S: relation) :=
  fun P Q => exists A, (R P A) /\ (S A Q).

Definition progresses (R : relation) S : Prop :=
  (forall P Q l Q', lts Q l Q' -> R P Q -> exists P', lts P l P' /\ S P' Q') /\
  (forall P Q l P', lts P l P' -> R P Q -> exists Q', lts Q l Q' /\ S P' Q').

Definition strongly_safe (F : relation -> relation) : Prop :=
  forall (R : relation) (S : relation),
    subset R S -> progresses R S ->
    (subset (F R) (F S) /\ progresses (F R) (F S)).

Definition preserves_symm F : Prop :=
  forall R, symmetric R -> symmetric (F R).

End Relations.

Module EarlyBisimProp.

Import EarlyBisim.
Import Syntax.
Import Relations.

(*Theorem progresses_bisim : forall R, progresses R R -> early_bisimulation R.
Proof.
  intros. unfold progresses in H; unfold early_bisimulation.
  split. eapply H. intros; eapply H; eauto. 
Qed.*)
(* Need to take symmetric closure here *)

Theorem progresses_subset_left :
  forall R S T, subset R S -> progresses S T ->
                progresses R T.
Proof.
  intros. unfold progresses in *. repeat split; eauto.
  - destruct H0. intros.  eapply H0 in H2. destruct H2 as [Q'0].
    exists Q'0. split; eapply H2. apply H. apply H3.
  - destruct H0. intros. eapply H1 in H2. destruct H2 as [Q'0]. 
    exists Q'0. eapply H2. apply H. apply H3.
Qed.

Theorem progresses_subset_right :
  forall R S T, subset S T -> progresses R S ->
                progresses R T.
Proof.
  intros. unfold progresses in *. repeat split; eauto.
  - destruct H0. intros. eapply H0 in H2. destruct H2 as [P'].
    exists P'. split. eapply H2. eapply H. eapply H2. eapply H3.
  - destruct H0. intros. eapply H1 in H2. destruct H2 as [Q'].
    exists Q'. split. eapply H2. eapply H. eapply H2. eapply H3.
Qed.

Fixpoint apply_n n R (F : relation -> relation) :=
  match n with
    | O => R
    | S n' => fun P Q => apply_n n' R F P Q \/ F (apply_n n' R F) P Q
  end.

Lemma apply_n_symm :
  forall n R F, symmetric R -> preserves_symm F ->
                symmetric (apply_n n R F).
Proof.
  intros. induction n.
  - simpl; eauto.
  - simpl. unfold symmetric. intros.
    destruct H1. left; eauto. right; eauto. eapply H0 in IHn.
    eauto.
Qed.

Lemma apply_n_subset :
  forall R F n, subset (apply_n n R F) (apply_n (S n) R F).
Proof.
  intros. simpl. unfold subset. intros. left; eapply H. 
Qed.

Lemma progresses_union :
  forall R1 R2 S, progresses R1 S -> progresses R2 S -> progresses (fun P Q => R1 P Q \/ R2 P Q) S.
Proof.
  intros. unfold progresses. repeat split.
  - intros.
    destruct H as [H _]. destruct H0 as [H0 _].
    destruct H2.
    + eapply H in H1. apply H1. apply H2.
    + eapply H0 in H1. apply H1. apply H2.
  - intros.
    destruct H as [_ H]. destruct H0 as [_ H0].
    destruct H2.
    + eapply H in H1. eapply H1. apply H2.
    + eapply H0 in H1. eapply H1. apply H2.
Qed.

Theorem apply_n_progresses :
  forall (R : relation) F n, strongly_safe F -> progresses R (F R) ->
                             progresses (apply_n n R F) (apply_n (S n) R F).
Proof.
  intros. induction n.
  - simpl. eapply progresses_subset_right; try (apply H0).
    unfold subset. intros; eauto.
  - simpl in *. eapply progresses_union.
    + eapply progresses_subset_right; try (apply IHn).
      unfold subset. intros. left. apply H1.
    + eapply progresses_subset_right with (F (fun P Q => apply_n n R F P Q \/ F (apply_n n R F) P Q)).
      unfold symmetric. intros. 
      unfold subset; intros. right; eauto. eapply H in IHn.
      apply IHn.
      unfold subset; intros. left; eauto.
Qed.

Theorem strongly_safe_in_bisimulation :
  forall (R : relation) F, preserves_symm F -> symmetric R -> strongly_safe F -> progresses R (F R) ->
                           early_bisimulation (fun P Q => exists n, apply_n n R F P Q).
Proof.
  intros. unfold early_bisimulation. unfold progresses in H2. split.
  - intros. destruct H3 as [n]. generalize dependent P1. generalize dependent P2.
    induction n.
    + intros. simpl in H3. exists 0; simpl; eauto.
    + intros. simpl in H3. destruct H3.
      * eapply IHn; eauto.
      * exists (S n). simpl. right.
        assert (symmetric (apply_n n R F)).
        { eapply apply_n_symm. apply H0. apply H. }
        apply H in H4. apply H4. apply H3.
  - intros. destruct H3 as [n]. eapply apply_n_progresses in H3; eauto.
    destruct H3 as [P2']. exists P2'.
    split. eapply H3.  exists (S n); eapply H3.
Qed.

Fixpoint iterate n (F : relation -> relation) (R : relation) :=
  match n with
    | O => F R
    | S n => r_compose (F R) (iterate n F R)
  end.

Theorem iterate_sum :
  forall F R P A Q n m, iterate n F R P A -> iterate m F R A Q ->
                        iterate (S (n + m)) F R P Q.
Proof.
  intros. generalize dependent P. induction n.
  - intros. simpl. simpl in H. exists A; eauto.
  - intros. simpl. simpl in H. simpl in IHn. inversion H; subst.
    exists x. split. eapply H1. eapply IHn. eapply H1.
Qed.

(*Theorem iterate_symmetric :
  forall n R F, symmetric R ->
                (forall f, symmetric f -> symmetric (F f)) ->
                symmetric (iterate n F R).
Proof.
  intros. induction n; eauto.
  simpl. unfold symmetric. intros. inversion H1; subst.
  - eapply symm_backwards. eapply H2. eapply H3.
  - eapply symm_forwards. eapply H2. eapply H3.
Qed.*)

Definition closure F R :=
  fun P Q => exists n, iterate n F R P Q.

Theorem closure_compose :
  forall A P Q F R, closure F R P A -> closure F R A Q -> closure F R P Q.
Proof.
  intros. destruct H. destruct H0.
  exists (1 + x + x0). eapply iterate_sum. eapply H. eapply H0.
Qed.
  
(*Theorem closure_symmetric :
  forall R F, symmetric R ->
              (forall f, symmetric f -> symmetric (F f)) ->
              symmetric (closure F R).
Proof.
  intros. unfold symmetric. intros. destruct H1 as [n].
  exists n.
  eapply iterate_symmetric; eauto.
Qed.*)

Theorem iterate_progresses :
  forall (R : relation) S F n,
    (forall f, symmetric f -> symmetric (F f)) ->
    (forall R S, subset R S -> progresses R S ->
     (subset (F R) (closure F S) /\ (progresses (F R) (closure F S)))) ->
    subset R S -> progresses R S ->
    (subset (iterate n F R) (closure F S) /\ (progresses (iterate n F R) (closure F S))).
Proof.
  intros. generalize dependent R. generalize dependent S. induction n.
  - intros; split.
    + simpl. unfold closure. unfold subset. intros.
      eapply H0; eauto.
    + simpl. unfold closure. unfold progresses. repeat split.
      * intros. eapply H0 in H1; eauto. eapply H1. eapply H3. eapply H4.
      * intros. eapply H0 in H1; eauto. eapply H1. eapply H3. eapply H4.
  - intros. split.
    + unfold subset. simpl. intros. destruct H3 as [A]; subst. destruct H3.
      assert (progresses R S); eauto.
      apply IHn in H2; eauto. destruct H2 as [H2 H2']. eapply H2 in H4.
      eapply H0 in H1; eauto. destruct H1. eapply H1 in H3. destruct H3 as [n']. destruct H4 as [n'']. exists (1 + (n' + n'')). eapply iterate_sum; eauto.
    + repeat split.
      * intros. simpl in H4. destruct H4 as [A]. destruct H4.
        assert (subset R S); eauto.
        eapply IHn in H6; eauto.
        assert (subset R S); eauto. eapply H0 in H7; eauto.
        destruct H7.
        destruct H8 as [H8 _].
        destruct H6 as [_ H6]. destruct H6 as [H6 _]. eapply H6 in H5.
        destruct H5. destruct H5.
        eapply H8 in H4. destruct H4. destruct H4.
        Focus 2. eapply H5. Focus 2. eapply H3. exists x0.
        split. eapply H4. eapply closure_compose. eapply H10. eapply H9.
      * intros. simpl in H4. destruct H4 as [A]. destruct H4.
        assert (subset R S); eauto.
        eapply IHn in H6; eauto.
        assert (subset R S); eauto. eapply H0 in H7; eauto.
        destruct H7.
        destruct H8 as [_ H8].
        destruct H6 as [_ H6]. destruct H6 as [_ H6].
        eapply H8 in H4. destruct H4. destruct H4.
        eapply H6 in H5. destruct H5. destruct H5.
        Focus 2. eapply H4. Focus 2. eapply H3. exists x0.
        split. eapply H5. eapply closure_compose. eapply H9. eapply H10.
Qed.

Theorem closure_safe :
  forall F, (forall f, symmetric f -> symmetric (F f)) ->
            (forall R S, subset R S -> progresses R S ->
                         subset (F R) (closure F S) /\ (progresses (F R) (closure F S))) ->
            strongly_safe (closure F).
Proof.
  intros.
  unfold closure. unfold strongly_safe. intros. split.
  - unfold subset. intros. destruct H3 as [n]. eapply iterate_progresses; eauto.
  - unfold progresses. repeat split.
    + intros. destruct H4. eapply iterate_progresses in H1; eauto. eapply H1; eauto.
    + intros. destruct H4. eapply iterate_progresses in H1; eauto. eapply H1; eauto.
Qed.

End EarlyBisimProp.

Module Contexts.

Import Syntax.
Import Semantics.
Import EarlyBisimProp.
Import EarlyBisim.
Import Relations.
  
Inductive ni_context : Type :=
| ni_output : channel -> channel -> ni_context -> ni_context
| ni_replicate : ni_context -> ni_context
| ni_compose_l : ni_context -> process -> ni_context
| ni_compose_r : process -> ni_context -> ni_context
| ni_hole : ni_context
.

Fixpoint ni_fill (nc : ni_context) (p : process) : process :=
  match nc with
    | ni_hole => p
    | ni_output c1 c2 c => output c1 c2 (ni_fill c p)
    | ni_replicate nic => replicate (ni_fill nic p)
    | ni_compose_l nic r => compose (ni_fill nic p) r
    | ni_compose_r l nic => compose l (ni_fill nic p)
  end.

Fixpoint ni_compose nc1 nc2 :=
  match nc1 with
    | ni_hole => nc2
    | ni_output c1 c2 c => ni_output c1 c2 (ni_compose c nc2)
    | ni_replicate nic => ni_replicate (ni_compose nic nc2)
    | ni_compose_l nic r => ni_compose_l (ni_compose nic nc2) r
    | ni_compose_r l nic => ni_compose_r l (ni_compose nic nc2)
  end.

Theorem ni_compose_fill :
  forall nc1 nc2 P,
    ni_fill nc1 (ni_fill nc2 P) = ni_fill (ni_compose nc1 nc2) P.
Proof.
  intros. induction nc1; try (simpl; rewrite IHnc1; eauto).
  - simpl. eauto.
Qed.

Definition ni_context_relation (R: relation) : relation :=
  fun P Q => exists (C : ni_context) P' Q',
               R P' Q' /\ P = (ni_fill C P') /\ Q = (ni_fill C Q').

Lemma ni_context_helper :
  forall x R P Q C,
    iterate x ni_context_relation R P Q ->
    iterate x ni_context_relation R (ni_fill C P) (ni_fill C Q).
Proof.
  intros. generalize dependent P. generalize dependent Q. induction x; simpl in *.
  - intros. destruct H as [C'].  destruct H as [P']. destruct H as [Q'].
    exists (ni_compose C C'). exists P'. exists Q'.
    repeat split.
    + eapply H.
    + destruct H. destruct H0. rewrite H0. rewrite ni_compose_fill. eauto.
    + destruct H. destruct H0. rewrite H1. rewrite ni_compose_fill. eauto.
  - intros. destruct H. destruct H. eapply IHx in H0. destruct H as [C'].
    destruct H as [P']. destruct H as [Q']. unfold r_compose.
    exists (ni_fill C x0). split; try (eapply H0).
    exists (ni_compose C C'). exists P'. exists Q'.
    repeat split.
    + eapply H.
    + destruct H. destruct H1. rewrite H1. rewrite ni_compose_fill. eauto.
    + destruct H. destruct H1. rewrite H2. rewrite ni_compose_fill. eauto.
Qed.
 
Lemma ni_context_progresses :
  forall P P' Q C R S l,
    subset R S -> progresses R S -> lts (ni_fill C P) l P' -> R P Q ->
    exists Q', lts (ni_fill C Q) l Q' /\ closure ni_context_relation S P' Q'. 
Proof.
  intros. generalize dependent l. generalize dependent P'. induction C.
  - intros. simpl in *. inversion H1; subst.
    exists (ni_fill C Q). split. constructor. exists 0. simpl.
    exists C. exists P. exists Q. repeat split. eapply H. eapply H2.
  - intros. simpl in *. inversion H1; subst.
    + eapply IHC in H4. destruct H4 as [Q']. destruct H3.
      exists (compose Q' (replicate (ni_fill C Q))). split.
      * eapply lts_rep_act. eapply H3.
      * destruct H4.
        exists (1 + x). simpl.
        exists (compose P'0 (replicate (ni_fill C Q))).
        split.
        exists (ni_compose_r P'0 (ni_replicate C)).
        exists P. exists Q. repeat split. eauto. 
        apply ni_context_helper with (C := (ni_compose_l ni_hole (replicate (ni_fill C Q)))) in H4. eapply H4.
    + eapply IHC in H4. eapply IHC in H5. destruct H4. destruct H3.
      destruct H5. destruct H5.
      exists (compose (compose x x0) (replicate (ni_fill C Q))).
      split.
      * eapply lts_rep_comm. eapply H3. eapply H5.
      * destruct H4 as [m]. destruct H6 as [m'']. exists (2 + m + m'').
        simpl. exists (compose (compose P'0 P'') (replicate (ni_fill C Q))).
        split. exists (ni_compose_r (compose P'0 P'') (ni_replicate C)).
        exists P. exists Q. repeat split. eauto.
        eapply iterate_sum.
        apply ni_context_helper with (C := (ni_compose_l (ni_compose_l ni_hole P'') (replicate (ni_fill C Q)))) in H4. eapply H4.
        simpl. apply ni_context_helper with (C := (ni_compose_l (ni_compose_r x ni_hole) (replicate (ni_fill C Q)))) in H6. eapply H6.
  - intros. inversion H1; subst.
    + eapply IHC in H7. destruct H7. destruct H3. exists (compose x p). split.
      * simpl. eapply lts_comp_left. eapply H3.
      * destruct H4. exists (x0).
        apply ni_context_helper with (C := (ni_compose_l ni_hole p)) in H4. eapply H4.
    + simpl in *. exists (compose (ni_fill C Q) Q'). split.
      * eapply lts_comp_right. eapply H7.
      * exists 0. simpl. exists (ni_compose_l C Q'). exists P. exists Q.
        repeat split; eauto.
    + eapply IHC in H5. destruct H5 as [Q0]. destruct H3. simpl.
      exists (compose Q0 Q'). split.
      * eapply lts_comm_left. eapply H3. eapply H8.
      * destruct H4. exists x.
        apply ni_context_helper with (C := ni_compose_l ni_hole Q') in H4. eapply H4.
    + eapply IHC in H5. destruct H5 as [Q0].  destruct H3. simpl.
      exists (compose Q0 Q'). split.
      * eapply lts_comm_right; eauto.
      * destruct H4 as [n']. exists n'.
        apply ni_context_helper with (C := ni_compose_l ni_hole Q') in H4. eapply H4.
  - intros. inversion H1; subst.
    + simpl in *. exists (compose P'0 (ni_fill C Q)). split.
      * eapply lts_comp_left. eapply H7.
      * exists 0. simpl. exists (ni_compose_r P'0 C). exists P. exists Q.
        repeat split; eauto.
    + eapply IHC in H7. destruct H7. destruct H3. exists (compose p x). split.
      * simpl. eapply lts_comp_right. eapply H3.
      * destruct H4. exists (x0).
        apply ni_context_helper with (C := (ni_compose_r p ni_hole)) in H4. eapply H4.
    + eapply IHC in H8. destruct H8 as [Q0]. destruct H3. simpl.
      exists (compose P'0 Q0). split.
      * eapply lts_comm_left. eapply H5. eapply H3.
      * destruct H4. exists x.
        apply ni_context_helper with (C := ni_compose_r P'0 ni_hole) in H4. eapply H4.
    + eapply IHC in H8. destruct H8 as [Q0].  destruct H3. simpl.
      exists (compose P'0 Q0). split.
      * eapply lts_comm_right; eauto.
      * destruct H4 as [n']. exists n'.
        apply ni_context_helper with (C := ni_compose_r P'0 ni_hole) in H4. eapply H4.
  - intros. simpl in *. eapply H0 in H1; eauto. destruct H1 as [Q']. exists Q'.
    split. eapply H1. exists 0. simpl. exists ni_hole. simpl.
    exists P'. exists Q'. repeat split; eauto. eapply H1.
Qed.

Lemma ni_context_progresses' :
  forall P Q' Q C R S l,
    subset R S -> progresses R S -> lts (ni_fill C Q) l Q' -> R P Q ->
    exists P', lts (ni_fill C P) l P' /\ closure ni_context_relation S P' Q'. 
Proof.
  intros. generalize dependent l. generalize dependent Q'. induction C.
  - intros. simpl in *. inversion H1; subst.
    exists (ni_fill C P). split. constructor. exists 0. simpl.
    exists C. exists P. exists Q. repeat split. eauto.
  - intros. simpl in *. inversion H1; subst.
    + eapply IHC in H4. destruct H4 as [Q']. destruct H3.
      exists (compose Q' (replicate (ni_fill C P))). split.
      * eapply lts_rep_act. eapply H3.
      * destruct H4.
        exists (1 + x). simpl.
        exists (compose Q' (replicate (ni_fill C Q))).
        split.
        exists (ni_compose_r Q' (ni_replicate C)).
        exists P. exists Q. repeat split. eauto. 
        apply ni_context_helper with (C := (ni_compose_l ni_hole (replicate (ni_fill C Q)))) in H4. eapply H4.
    + eapply IHC in H4. eapply IHC in H5. destruct H4. destruct H3.
      destruct H5. destruct H5.
      exists (compose (compose x x0) (replicate (ni_fill C P))).
      split.
      * eapply lts_rep_comm. eapply H3. eapply H5.
      * destruct H4 as [m]. destruct H6 as [m'']. exists (2 + m + m'').
        simpl. exists (compose (compose x x0) (replicate (ni_fill C Q))).
        split. exists (ni_compose_r (compose x x0) (ni_replicate C)).
        exists P. exists Q. repeat split. eauto.
        eapply iterate_sum.
        apply ni_context_helper with (C := (ni_compose_l (ni_compose_l ni_hole x0) (replicate (ni_fill C Q)))) in H4. simpl in H4. eapply H4.
        simpl. apply ni_context_helper with (C := (ni_compose_l (ni_compose_r P' ni_hole) (replicate (ni_fill C Q)))) in H6. eapply H6.
  - intros. inversion H1; subst.
    + eapply IHC in H7. destruct H7. destruct H3. exists (compose x p). split.
      * simpl. eapply lts_comp_left. eapply H3.
      * destruct H4. exists (x0).
        apply ni_context_helper with (C := (ni_compose_l ni_hole p)) in H4. eapply H4.
    + simpl in *. exists (compose (ni_fill C P) Q'0). split.
      * eapply lts_comp_right. eapply H7.
      * exists 0. simpl. exists (ni_compose_l C Q'0). exists P. exists Q.
        repeat split; eauto.
    + eapply IHC in H5. destruct H5 as [Q0]. destruct H3. simpl.
      exists (compose Q0 Q'0). split.
      * eapply lts_comm_left. eapply H3. eapply H8.
      * destruct H4. exists x.
        apply ni_context_helper with (C := ni_compose_l ni_hole Q'0) in H4. eapply H4.
    + eapply IHC in H5. destruct H5 as [Q0].  destruct H3. simpl.
      exists (compose Q0 Q'0). split.
      * eapply lts_comm_right; eauto.
      * destruct H4 as [n']. exists n'.
        apply ni_context_helper with (C := ni_compose_l ni_hole Q'0) in H4. eapply H4.
  - intros. inversion H1; subst.
    + simpl in *. exists (compose P' (ni_fill C P)). split.
      * eapply lts_comp_left. eapply H7.
      * exists 0. simpl. exists (ni_compose_r P' C). exists P. exists Q.
        repeat split; eauto.
    + eapply IHC in H7. destruct H7. destruct H3. exists (compose p x). split.
      * simpl. eapply lts_comp_right. eapply H3.
      * destruct H4. exists (x0).
        apply ni_context_helper with (C := (ni_compose_r p ni_hole)) in H4. eapply H4.
    + eapply IHC in H8. destruct H8 as [Q0]. destruct H3. simpl.
      exists (compose P' Q0). split.
      * eapply lts_comm_left. eapply H5. eapply H3.
      * destruct H4. exists x.
        apply ni_context_helper with (C := ni_compose_r P' ni_hole) in H4. eapply H4.
    + eapply IHC in H8. destruct H8 as [Q0].  destruct H3. simpl.
      exists (compose P' Q0). split.
      * eapply lts_comm_right; eauto.
      * destruct H4 as [n']. exists n'.
        apply ni_context_helper with (C := ni_compose_r P' ni_hole) in H4. eapply H4.
  - intros. simpl in *. destruct H0. eapply H0 in H1; eauto.
    destruct H1 as [P']. exists P'.
    split. eapply H1. exists 0. simpl. exists ni_hole. simpl.
    exists P'. exists Q'. repeat split; eauto. eapply H1.
Qed.

Theorem strongly_safe_ni_context : strongly_safe (closure ni_context_relation).
  eapply closure_safe.
  - intros. unfold symmetric. intros. unfold ni_context_relation.
    unfold ni_context_relation in H0.  destruct H0 as [C].
    destruct H0 as [P']. destruct H0 as [Q'].
    exists C. exists Q'. exists P'.
    destruct H0. destruct H1.
    repeat split; eauto.
  - intros. split.
    + unfold subset. intros.
      exists 0. simpl. unfold ni_context_relation in *.
      destruct H1 as [C]. destruct H1 as [P']. destruct H1 as [Q'].
      exists C. exists P'. exists Q'.
      destruct H1. destruct H2.
      repeat split; eauto.
    + unfold progresses. split.
      * intros. destruct H2 as [C]. destruct H2 as [P']. destruct H2 as [Q_fill].
        destruct H2. destruct H3. subst.
        eapply ni_context_progresses'; eauto.
      * intros. destruct H2 as [C]. destruct H2 as [P_fill]. destruct H2 as [Q']. 
        destruct H2. destruct H3. subst.
        eapply ni_context_progresses; eauto.
Qed.

End Contexts.