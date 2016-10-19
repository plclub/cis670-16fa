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

Lemma tt_unit : exp d_empty g_empty tt unit.
Proof.
  unfold unit. unfold tt.
  pick fresh X and apply exp_Lam.
  unfold open_Exp_wrt_Typ. unfold open_Typ_wrt_Typ.
  simpl.
  pick fresh x and apply exp_lam.
  auto.
  unfold open_Exp_wrt_Exp. simpl.
  eapply exp_var.
  auto.
  auto.
  auto.
  auto.
Qed.

Definition prod (t1 t2 : Typ) : Typ :=
  t_all (t_arr (t_arr t1 (t_arr t2 (t_var_b 0))) (t_var_b 0)).

Definition sum (t1 t2 : Typ) : Typ :=
  t_all (t_arr (t_arr t1 (t_var_b 0)) (t_arr (t_arr t2 (t_var_b 0)) (t_var_b 0))).

Definition num : Typ :=
  t_all (t_arr (t_var_b 0) (t_arr (t_arr (t_var_b 0) (t_var_b 0)) (t_var_b 0))).

