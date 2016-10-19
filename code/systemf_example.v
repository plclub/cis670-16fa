Add LoadPath "/Users/sweirich/github/deepspec/metalib/" as Metalib.
Require Import Metalib.Metatheory.

Require Import systemf_ott.

Definition void := t_all (t_var_b 0).

Definition unit := t_all (t_arr (t_var_b 0) (t_var_b 0)).
Definition tt   := e_Lam (e_lam (t_var_b 0) (e_var_b 0)).

Lemma lc_Typ_void : lc_Typ void.
Proof.
  eapply lc_t_all. intro X.
  unfold open_Typ_wrt_Typ. simpl.
  eapply lc_t_var_f.
Qed.

Lemma tt_unit : exp nil nil tt unit.
Proof.
  unfold unit. unfold tt.
  pick fresh X and apply exp_Lam.
  unfold open_Exp_wrt_Typ. unfold open_Typ_wrt_Typ.
  simpl.
  pick fresh x and apply exp_lam.
  constructor; repeat (try (left; reflexivity); right).
  unfold open_Exp_wrt_Exp. simpl.
  eapply exp_var; constructor; repeat (try (left; reflexivity); right).
  auto.
Qed.



Definition prod (t1 t2 : Typ) : Typ :=
  t_all (t_arr (t_arr t1 (t_arr t2 (t_var_b 0))) (t_var_b 0)).

Definition pair : Exp :=
  e_Lam
    (e_Lam
       (e_lam (t_var_b 1)
          (e_lam (t_var_b 0)
                 (e_Lam
                    (e_lam (t_arr (t_var_b 2) (t_arr (t_var_b 1) (t_var_b 0)))
                           (e_ap (e_ap (e_var_b 0) (e_var_b 2)) (e_var_b 1))))))).

Lemma pair_typing : 
  exp nil nil pair (t_all (t_all (t_arr (t_var_b 1)
                                                (t_arr (t_var_b 0)
                                             (prod (t_var_b 2) (t_var_b 1)))))).
Proof.
  intros.
  unfold pair, prod.
  pick fresh X and apply exp_Lam.
  unfold open_Exp_wrt_Typ, open_Typ_wrt_Typ. simpl.
  pick fresh Y and apply exp_Lam.
  unfold open_Exp_wrt_Typ, open_Typ_wrt_Typ. simpl.

  pick fresh x and apply exp_lam.
  constructor; repeat (try (left; reflexivity); right).
  unfold open_Exp_wrt_Exp. simpl.

  pick fresh y and apply exp_lam.
  constructor; repeat (try (left; reflexivity); right).
  unfold open_Exp_wrt_Exp. simpl.

  pick fresh Z and apply exp_Lam.
  unfold open_Exp_wrt_Typ, open_Typ_wrt_Typ. simpl.

  pick fresh z and apply exp_lam.
  repeat eapply type_arr; constructor; repeat (try (left; reflexivity); right).
  
  unfold open_Exp_wrt_Exp. simpl.
  repeat eapply exp_ap; repeat (constructor; repeat (try (left; reflexivity); right)).
Qed.

Definition sum (t1 t2 : Typ) : Typ :=
  t_all (t_arr (t_arr t1 (t_var_b 0)) (t_arr (t_arr t2 (t_var_b 0)) (t_var_b 0))).

Definition num : Typ :=
  t_all (t_arr (t_var_b 0) (t_arr (t_arr (t_var_b 0) (t_var_b 0)) (t_var_b 0))).

