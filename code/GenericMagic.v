(* Now for something cooler *)

(* Again, sums and products *)
Inductive ty := 
| ty_unit : ty
| ty_sum  : ty -> ty -> ty
| ty_prod : ty -> ty -> ty.

(* Each "ty" denotes a Coq Type *)
Fixpoint denote (t : ty) : Type :=
  match t with
    | ty_unit => unit
    | ty_prod t1 t2 => (denote t1 * denote t2)
    | ty_sum  t1 t2 => (denote t1 + denote t2)
  end.

(* Dependent types are cool! *)
Require Import String. Open Scope string.

Fixpoint generic_print (ty : ty) : denote ty -> string :=
  match ty return forall x : denote ty, string with
    | ty_unit => fun x => "()"
    | ty_prod t1 t2 =>
      fun x => "(" ++ generic_print t1 (fst x) ++ " , "
                   ++ generic_print t2 (snd x) ++ ")" 
    | ty_sum t1 t2 =>
      fun x => match x with
                 | inl a => "(inl " ++ generic_print t1 a ++ ")"
                 | inr b => "(inr " ++ generic_print t2 b ++ ")"
               end
  end.

Eval compute in generic_print (ty_sum ty_unit ty_unit) (inl tt).
Eval compute in generic_print (ty_prod ty_unit (ty_sum ty_unit ty_unit)) 
                              (tt, inr tt).

(* Back to type operators *)
Inductive typ_op : Set :=
| t_hole : typ_op
| t_unit : typ_op
| t_sum  : typ_op -> typ_op -> typ_op
| t_prod : typ_op -> typ_op -> typ_op.

Fixpoint subst_typ_op (r : ty) (t : typ_op) : ty :=
  match t with
    | t_hole => r
    | t_unit => ty_unit
    | t_sum  t1 t2 => ty_sum  (subst_typ_op r t1) (subst_typ_op r t2)
    | t_prod t1 t2 => ty_prod (subst_typ_op r t1) (subst_typ_op r t2)
  end.

Fixpoint generic_map (to : typ_op) :
  forall (ta tb : ty),
    (denote ta -> denote tb) ->
    denote (subst_typ_op ta to) -> denote (subst_typ_op tb to) :=
  match to return forall (ta tb : ty),
                    (denote ta -> denote tb) ->
                    denote (subst_typ_op ta to) -> denote (subst_typ_op tb to) with
    | t_hole =>
      fun ta tb f x => f x
    | t_unit => fun _ _ _ _ => tt
    | t_prod t1 t2 =>
      fun ta tb f x =>
        (generic_map t1 ta tb f (fst x), generic_map t2 ta tb f (snd x))
    | t_sum t1 t2 =>
      fun ta tb f x =>
        match x with
          | inl a => inl (generic_map t1 ta tb f a)
          | inr b => inr (generic_map t2 ta tb f b)
        end
  end.

Eval compute in
    generic_map (t_sum t_hole t_unit) ty_unit
                (ty_prod ty_unit ty_unit)
                (fun _ => (tt, tt)) (inl tt).

Theorem generic_map_id :                          
  forall to ta e, generic_map to ta ta (fun x => x) e = e.
Proof.
  induction to; intros; subst; simpl in *; eauto.
  - destruct e; auto.
  - destruct e; subst; f_equal; eauto.
  - destruct e; subst. f_equal; eauto.
Qed.


Definition generic_eq ty : forall (x y : denote ty), {x = y} + {x <> y}.
induction ty; intros.
+ destruct x; destruct y; left; reflexivity.
+ destruct x as [x1 | x2]; destruct y as [y1 | y2].
  - destruct (IHty1 x1 y1); subst.
    * left; reflexivity.
    * right; congruence.
  - right; congruence.
  - right; congruence.
  - destruct (IHty2 x2 y2); subst.
    * left; reflexivity.
    * right; congruence.
+ destruct x as [x1 x2]; destruct y as [y1 y2].
  destruct (IHty1 x1 y1); destruct (IHty2 x2 y2); subst;
  try solve [right; congruence];
  try solve [left; reflexivity].
Defined.

Eval compute in generic_eq (ty_prod ty_unit (ty_sum ty_unit ty_unit))
                           (tt, inr tt) (tt, inr tt).
Eval compute in generic_eq (ty_prod ty_unit (ty_sum ty_unit ty_unit))
                           (tt, inr tt) (tt, inl tt).

