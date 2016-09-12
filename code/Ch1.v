(* 

Commentary on Chapter 1
========================

This chapter provides the mathematical baseline for reasoning about
programming languages, by first introducing Abstract Syntax Trees (which
should be familiar to functional programmers who have worked with datatypes in
ML or Haskell) and then Abstract Binding Trees (which add lexical scoping to
ASTs).

This framework is taken as given in most programming languages research
papers, and we will assume in this course that everyone is familiar with the
reasoning principle of structural induction over datatypes. (See the
[Induction](https://www.cis.upenn.edu/~bcpierce/sf/current/Induction.html)
chapter of Software Foundations for background otherwise.)

*)

Require Import Metalib.Metatheory.

Module One.

(*

Variables and Abstract Syntax Trees
-----------------------------------

What makes a simple datatype an *abstract syntax tree* is the presence of
*variables*.

Harper defines Abstract Syntax Trees indexed by sets of variables, X. These
sets define what variables are allowed to appear in the syntax.

For example, we can define an indexed type in Coq that creates an abstract
syntax of for lambda calculus terms.  This datatype is indexed by a set of
variables X.

[NOTE: There is another detail that we're glossing over: each variable itself
comes with a `sort`, or tree that it is associated with. For simplicity now,
we'll assume that there is only one sort of syntax (called `exp`) and
consequently only one sort of variable.]
 *)

Inductive exp (X : vars): Set :=
| Var : forall (x:var), x \in X -> exp X
| App : forall (a:exp X) (b:exp X),  exp X
.

(* 

This definition gives the same induction principle as in PFPL. We need to show that 
the property holds for all variables that could occur in the syntax. (i.e. for an 
arbitrary member of X).

*)

Check exp_ind.
(*
exp_ind
     : forall (X : atoms) (P : exp X -> Prop),
       (forall (x : atom) (i : x `in` X), P (Var X x i)) ->
       (forall a : exp X, P a -> forall b : exp X, P b -> P (App X a b)) ->
       forall e : exp X, P e
 *)

Program Fixpoint subsume_vars X Y (pf: X [<=] Y) (a: exp X) {struct a} : exp Y :=
  match a with
  | Var _ y _ => Var _ y _
  | App _ a1 a2 => App _ (subsume_vars _ _ _ a1) (subsume_vars _ _ _ a2)
  end.

(* With effort, we can also define substitution for these indexed expressions (justifying
   Theorem 1.1), using the metatheory library to prove a small fact about set
   membership. 
*)
Program Fixpoint subst_exp X x (a : exp (add x X)) (b: exp X) {struct a} : exp X :=
  match a with
  | Var _ y _   => if eq_var x y then b else (Var _ y _)
  | App _ a1 a2 => App _ (subst_exp X x a1 b) (subst_exp X x a2 b)
  end.
Obligation 1.
fsetdec.
Qed.

(*
Note however, that it is not so smooth to work with indexed data structures in Coq, as you 
must simultanously define operations and prove how they interact with variables.
We won't be doing so in future examples. 
*)

End One.

Module Two.

(*  
Abstract Binding Trees
----------------------

On the other hand, scope and binding is more subtle than it seems. The reason
for this is the mathematical maturity required to work "up-to
alpha-equivalence".  In otherwords, when we work with abstract binding trees,
we are not working with individual abstract syntax trees, we are working with
an equivalence class of trees, defined by the alpha-equivalence relation.

 *)

  Parameter x : var.
  Parameter y : var.
  Parameter z : var.

  Axiom fr1 : x <> y.
  Axiom fr2 : y <> z.
  Axiom fr3 : x <> z.
  
  Inductive exp : Set :=
  | Var (x:var)
  | App (a:exp) (b:exp)
  | Abs (x:var) (a:exp).

  (* Calculate the variables occurring free in a particular expression. *)

  Fixpoint fv (a : exp) : vars :=
    match a with
    | Var x => {{ x }}
    | App a1 a2 => fv a1 \u fv a2
    | Abs x a1 => remove x (fv a1)
    end.
  
(*

Two trees are alpha-equivalent when they differ only in the names
of bound variables.

For example: 

      \x. \y. x     ==alpha   \y.\z.y       (can swap x and y to make them equal)

but not

      \x. \y. z     /==alpha  \x.\y.w       (differ in free variables)


There are many ways to define exactly *when* two trees are alpha
equivalent. In this file, we will compare two different ones, both based on renamings.
See naive_aeq and aeq below.

*)

  
  (* A renaming is a bijection between variable names *)
  Definition renaming := (var * var)%type.

  (* If a given variable matches either of the names in the bijection it 
     is replaced with the other one. *)
  Fixpoint rename_var (rho : renaming) (x:var) :=
    match rho with
    | (y,z) => if x == y then z else if x == z then y else x
    end.

  (* ------------- properties about renaming variables --------- *)

  (* We are going to have to prove that EVERYTHING is stable under 
     renaming (also called equivariant).  

     This will get tiresome. To make the proofs (slightly) simpler, 
     we'll define a few tactics. *)

  (* A tactic for reasoning about variable equality. If the term 
     x == x appears in the goal, this tactic will reduce it. *)
  Ltac eq_var_refl a0 :=
    let NE := fresh in
    let E  := fresh in
    destruct (a0 == a0) as [_ | NE];
    [|unfold not in NE; assert False; auto; contradiction].
  (* Another tactic for reasoning about variable equality. If the 
     term x == y appears in the goal, and we have an assumption that 
     the two variables are not equal in the hypotheses, then 
     this tactic will reduce the goal. *)
  Ltac neq_var x y :=
    let K := fresh in
    match goal with
    | H : x <> y |- _ => destruct (x == y); [contradiction|]
    | H : y <> x |- _ => destruct (x == y) as [K|_]; [apply symmetry in K; contradiction|]
    end.

  

  (* A proof that renaming a variable twice brings you back where you started. *)
  Lemma self_inverse_var : forall rho x, rename_var rho (rename_var rho x) = x.
  Proof.
    intros rho x. destruct rho.
    simpl.
    destruct (x == a).
    + eq_var_refl a0.
      destruct (a0 == a); subst; auto.
    + destruct (x == a0). eq_var_refl a. auto.
      neq_var x a. neq_var x a0.
      auto.
  Qed.

  (* reordering the renaming is allowed *)
  Lemma rename_swap_var : forall x y z, rename_var (x,y) z = rename_var (y,x) z.
  Proof.
    intros x y x0. simpl.
    destruct (x0 == x). destruct (x0 == y). subst. auto. subst. auto. auto.
   Qed.

  
  (* renaming with the same variable does nothing *)
  Lemma rename_var_id : forall y x, rename_var (y,y) x = x.
  Proof.
    intros y x.
    simpl.
    destruct (x == y).
    auto. auto.
  Qed.

  (* renaming with a different variable does something *)
  Lemma rename_var_diff : forall x1 x2, x1 <> x2 -> rename_var  (x1, x2) x2  = x1.
  Proof.
    intros. simpl. neq_var x2 x1. eq_var_refl x2. auto.
  Qed.

  (* we can push renamings through eachother *)
  Lemma commute_var : forall x z rho x0,
      (rename_var (rename_var rho x,rename_var rho z) (rename_var rho x0)) =
      rename_var rho (rename_var (x,z) x0).
  Proof.
    intros x z rho x0. destruct rho as (y1,y2). simpl.
      destruct (x0 == x). subst.
      eq_var_refl (if x == y1 then y2 else if x == y2 then y1 else x). auto.
      destruct (x0 == z). subst.
      + eq_var_refl (if z == y1 then y2 else if z == y2 then y1 else z).
        destruct (z == y1). destruct (x == y1). eq_var_refl y2. auto.
        destruct (x == y2). subst.
        neq_var y2 y1. auto.
        neq_var y2 x. auto.
        destruct (z == y2). destruct (x == y1). subst. neq_var y1 y2. auto.
        destruct (x == y2). subst. eq_var_refl y1. auto.
        neq_var y1 x. auto.
        destruct (x == y1). subst. neq_var z y2. auto.
        destruct (x == y2). neq_var z y1. auto. neq_var z x. auto.
      + destruct (x0 == y1). subst.
        neq_var x y1.
        destruct (x == y2). subst. neq_var y2 y1. neq_var z y1.
        destruct (z == y2). subst. neq_var y2 y1. auto.
        neq_var y2 z. auto.
        neq_var y2 x.
        neq_var z y1.
        destruct (z == y2). subst. neq_var y2 y1. auto. neq_var y2 z. auto.
        destruct (x0 == y2). subst.
        destruct (x == y1). subst. neq_var y1 y2.
        destruct (z == y1). subst. eq_var_refl y1. neq_var y1 y2. auto.
        neq_var z y2. neq_var y1 z. auto.
        neq_var x y2. neq_var y1 x.
        destruct (z == y1). neq_var y1 y2. auto. neq_var z y2.
        destruct (y1 == z). symmetry in e. contradiction. auto.
        destruct (x == y1). neq_var x0 y2.
        destruct (z == y1). neq_var x0 y2. auto.
        destruct (z == y2). neq_var x0 y1. auto. neq_var x0 z. auto.
        destruct (x == y2). neq_var x0 y1.
        destruct (z == y1). neq_var x0 y2. auto.
        destruct (z == y2). neq_var x0 y1. auto. neq_var x0 z. auto.
        neq_var x0 x.
        destruct (z == y1). neq_var x0 y2. auto.
        destruct (z == y2). neq_var x0 y1. auto. neq_var x0 z. auto.
  Qed.


  (* --------------------------------------------- *)
  (* ----- apply a renaming to an expression ----- *)
  
  Fixpoint rename rho (a:exp) :=
    match a with
    | Var x   => Var (rename_var rho x)
    | App a b => App (rename rho a) (rename rho b)
    | Abs x a => Abs (rename_var rho x) (rename rho a)
    end.

  (* ----- properties about renaming expressions ----- *)

  Lemma rename_id : forall y a, rename (y,y) a = a.
  Proof.
    intros y a. 
    induction a; unfold rename; fold rename.
    - rewrite rename_var_id. auto.
    - rewrite IHa1. rewrite IHa2. auto.
    - rewrite IHa. rewrite rename_var_id.
    auto.
  Qed.

  Lemma self_inverse : forall rho a, rename rho (rename rho a) = a.
  Proof.
    intros rho a. induction a; unfold rename; fold rename.
    - rewrite self_inverse_var. auto.
    - rewrite IHa1. rewrite IHa2. auto.
    - rewrite self_inverse_var. rewrite IHa. auto.
  Qed.


  Lemma rename_swap : forall x y a, rename (x,y) a = rename (y,x) a.
  Proof.
    intros x y a. induction a; unfold rename; fold rename.
    - rewrite rename_swap_var. auto.
    - rewrite IHa1. rewrite IHa2. auto.
    - rewrite rename_swap_var. rewrite IHa. auto.
  Qed.

  Lemma commute : forall x z rho a1,
      (rename (rename_var rho x, rename_var rho z) (rename rho a1)) =
      rename rho (rename (x, z) a1).
  Proof.
    intros x z rho a. induction a.
    - simpl. f_equal. pose (K := commute_var x z rho x0). clearbody K.
      simpl in K. auto.
    - simpl. rewrite IHa1. rewrite IHa2. auto.
    - simpl. f_equal.
      pose (K := commute_var x z rho x0). clearbody K.
      simpl in K. auto. auto.
  Qed.

  (* ---------------- renaming a set of variables ------------------ *)

  Definition rename_set rho S :=
    match rho with
      | (x,y) => 
        if AtomSetImpl.mem x S && AtomSetImpl.mem y S then S
        else if AtomSetImpl.mem x S then remove x (add y S)
             else if AtomSetImpl.mem y S then remove y (add x S)
                  else S
    end.

  (* --------- properties about renaming a set of variables ------------ *)

  Lemma self_inverse_set : forall rho S, rename_set rho (rename_set rho S) = S.
  Proof. 
    intros.
    destruct rho as [x y].
    simpl.
    destruct (AtomSetProperties.In_dec x S);
    destruct (AtomSetProperties.In_dec y S);
    try (rewrite AtomSetFacts.mem_iff in i; rewrite i);
    try (rewrite AtomSetFacts.mem_iff in i0; rewrite i0);
    try (rewrite AtomSetFacts.not_mem_iff in n; rewrite n);
    try (rewrite AtomSetFacts.not_mem_iff in n0; rewrite n0);
    simpl;
      try (rewrite i);
      try (rewrite i0);
      try (rewrite n);
      try (rewrite n0);
      auto.
  Admitted.

  Lemma rename_set_id : forall y S, rename_set (y,y) S = S.
  Proof. 
    intros. simpl.
    destruct (AtomSetProperties.In_dec y0 S).
    rewrite AtomSetFacts.mem_iff in i. rewrite i.
    simpl.  auto.
    rewrite AtomSetFacts.not_mem_iff in n. rewrite n.
    simpl. auto.
    Qed.

  Lemma rename_in : forall rho x X, x `in` X -> rename_var rho x `in` rename_set rho X.
  Proof. 
    intros.
    destruct rho as [x y].
    simpl.
    destruct (x0 == x).
    - subst.
      rewrite AtomSetFacts.mem_iff in H. rewrite H.
      simpl.
      destruct (AtomSetProperties.In_dec y X).
      + rewrite AtomSetFacts.mem_iff in i. rewrite i.
        rewrite AtomSetFacts.mem_iff. auto.
      + rewrite AtomSetFacts.not_mem_iff in n. rewrite n.
        assert (x <> y). unfold not. intro. subst. rewrite n in H. inversion H.
        fsetdec.
    -  destruct (x0 == y). subst.
       rewrite AtomSetFacts.mem_iff in H. rewrite H.
       destruct (AtomSetProperties.In_dec x X).
       rewrite AtomSetFacts.mem_iff in i. rewrite i.
       simpl. rewrite AtomSetFacts.mem_iff. auto.
       rewrite AtomSetFacts.not_mem_iff in n0. rewrite n0.
       simpl. fsetdec.
       destruct (AtomSetProperties.In_dec x X).
       rewrite AtomSetFacts.mem_iff in i. rewrite i.
      destruct (AtomSetProperties.In_dec y X).
       rewrite AtomSetFacts.mem_iff in i0. rewrite i0.
       simpl. auto.
       rewrite AtomSetFacts.not_mem_iff in n1. rewrite n1.
       simpl. fsetdec.
       rewrite AtomSetFacts.not_mem_iff in n1. rewrite n1.
      destruct (AtomSetProperties.In_dec y X).
       rewrite AtomSetFacts.mem_iff in i. rewrite i.
       simpl. fsetdec.
       rewrite AtomSetFacts.not_mem_iff in n2. rewrite n2.
       simpl. fsetdec.
  Qed.

  Lemma rename_union : forall X Y rho, 
      rename_set rho (X \u Y) [=] 
      (union (rename_set rho X) (rename_set rho Y)).
  Proof.
    intros X Y rho.
    destruct rho as [x y].
    simpl.
    rewrite (AtomSetFacts.union_b X Y x).
    rewrite (AtomSetFacts.union_b X Y y).
    destruct (AtomSetProperties.In_dec x X);
      destruct (AtomSetProperties.In_dec x Y);
      destruct (AtomSetProperties.In_dec y X);
      destruct (AtomSetProperties.In_dec y Y);
    try (rewrite AtomSetFacts.mem_iff in i; rewrite i);
    try (rewrite AtomSetFacts.mem_iff in i0; rewrite i0);
    try (rewrite AtomSetFacts.mem_iff in i1; rewrite i1);
    try (rewrite AtomSetFacts.mem_iff in i2; rewrite i2);
    try (rewrite AtomSetFacts.not_mem_iff in n; rewrite n);
    try (rewrite AtomSetFacts.not_mem_iff in n0; rewrite n0);
    try (rewrite AtomSetFacts.not_mem_iff in n1; rewrite n1);
    try (rewrite AtomSetFacts.not_mem_iff in n2; rewrite n2);
    try (rewrite <- AtomSetFacts.mem_iff in i);
    try (rewrite <- AtomSetFacts.mem_iff in i0);
    try (rewrite <- AtomSetFacts.mem_iff in i1);
    try (rewrite <- AtomSetFacts.mem_iff in i2);
    try (rewrite <- AtomSetFacts.not_mem_iff in n);
    try (rewrite <- AtomSetFacts.not_mem_iff in n0);
    try (rewrite <- AtomSetFacts.not_mem_iff in n1);
    try (rewrite <- AtomSetFacts.not_mem_iff in n2);
    simpl; try fsetdec.
    all: unfold AtomSetImpl.Equal;
    intros z; split; intros;
    destruct (z == x); subst; try fsetdec;
    destruct (z == y); subst; fsetdec.
    Qed.

  Lemma rename_remove : forall rho x s, remove (rename_var rho x) (rename_set rho s) [=] rename_set rho (remove x s).
  Proof.
    intros rho z S.
    destruct rho as [x y]. destruct (x == y). subst. rewrite rename_var_id. rewrite rename_set_id. rewrite rename_set_id. fsetdec.
    simpl.
    rewrite (AtomSetFacts.remove_b S z x).
    rewrite (AtomSetFacts.remove_b S z y).
    unfold AtomSetFacts.eqb. unfold KeySetFacts.eq_dec.
    destruct (eq_atom_dec z x); subst; eq_var_refl x.
    destruct (eq_atom_dec x y); [contradiction|idtac].
    destruct (AtomSetProperties.In_dec x S);
    destruct (AtomSetProperties.In_dec y S);
    try (rewrite AtomSetFacts.mem_iff in i; rewrite i);
    try (rewrite AtomSetFacts.mem_iff in i0; rewrite i0);
    try (rewrite AtomSetFacts.not_mem_iff in n1; rewrite n1);
    try (rewrite AtomSetFacts.not_mem_iff in n2; rewrite n2);
    try (rewrite <- AtomSetFacts.mem_iff in i);
    try (rewrite <- AtomSetFacts.mem_iff in i0);
    try (rewrite <- AtomSetFacts.not_mem_iff in n1);
    try (rewrite <- AtomSetFacts.not_mem_iff in n2);
    simpl; try fsetdec.
    unfold AtomSetImpl.Equal;
    intros z; split; intros;
    destruct (z == x); subst; try fsetdec;
      destruct (z == y); subst; fsetdec.
    neq_var z x.
    destruct (AtomSetProperties.In_dec x S);
    destruct (AtomSetProperties.In_dec y S);
    try (rewrite AtomSetFacts.mem_iff in i; rewrite i);
    try (rewrite AtomSetFacts.mem_iff in i0; rewrite i0);
    try (rewrite AtomSetFacts.not_mem_iff in n1; rewrite n1);
    try (rewrite AtomSetFacts.not_mem_iff in n2; rewrite n2);
    try (rewrite <- AtomSetFacts.mem_iff in i);
    try (rewrite <- AtomSetFacts.mem_iff in i0);
    try (rewrite <- AtomSetFacts.not_mem_iff in n1);
    try (rewrite <- AtomSetFacts.not_mem_iff in n2);
    simpl; try fsetdec.
    destruct (eq_atom_dec z y).
    subst. eq_var_refl y. simpl. 
    unfold AtomSetImpl.Equal;
    intros z; split; intros;
    destruct (z == x); subst; try fsetdec;
      destruct (z == y); subst; fsetdec.
    neq_var z y. simpl. fsetdec.
    destruct (eq_atom_dec z y).
    subst. eq_var_refl y. fsetdec.
    neq_var z y. fsetdec.
    destruct (eq_atom_dec z y). subst. eq_var_refl y. simpl. fsetdec.
    neq_var z y. simpl. fsetdec.
    destruct (AtomSetProperties.In_dec y S);
    try (rewrite AtomSetFacts.mem_iff in i; rewrite i);
    try (rewrite AtomSetFacts.not_mem_iff in n4; rewrite n4);
    try (rewrite <- AtomSetFacts.mem_iff in i);
    try (rewrite <- AtomSetFacts.not_mem_iff in n4);
    simpl; try fsetdec.
    destruct (z == y). subst. fsetdec. fsetdec.
  Qed.

    Lemma rename_singleton : forall rho x, rename_set rho (singleton x) [=] singleton (rename_var rho x).
  Proof.
    intros rho x. destruct rho as [y z].
    simpl.
    rewrite (AtomSetFacts.singleton_b).
    rewrite (AtomSetFacts.singleton_b).
    unfold AtomSetFacts.eqb. unfold KeySetFacts.eq_dec.
    destruct (eq_atom_dec x y).
    destruct (eq_atom_dec x z).
    simpl. subst. eq_var_refl y. subst. fsetdec.
    simpl. subst. eq_var_refl y. fsetdec.
    destruct (eq_atom_dec x z).
    simpl. subst. neq_var z y. eq_var_refl z. fsetdec.
    simpl. neq_var x y. neq_var x z. fsetdec.
  Qed.

  
  (* ------------ properties about renaming and fv ------------- *)

  (* equivariance for the fv function *)

  Lemma fv_rename : forall rho a, fv (rename rho a) [=] rename_set rho (fv a).
  Proof.
    intros rho a. induction a.
    - destruct rho as [x y].
      destruct (x == y). subst. rewrite rename_id. rewrite rename_set_id. fsetdec.
      simpl.
      rewrite (AtomSetFacts.singleton_b x0 x).
      rewrite (AtomSetFacts.singleton_b x0 y).
      unfold AtomSetFacts.eqb. unfold KeySetFacts.eq_dec.
      destruct (eq_atom_dec x0 x). subst. eq_var_refl x.
      simpl.
      destruct (eq_atom_dec x y). contradiction. fsetdec.
      neq_var x0 x.
      destruct (eq_atom_dec x0 y). subst. eq_var_refl y. simpl. fsetdec.
      neq_var x0 y. simpl. fsetdec.
    - simpl. rewrite IHa1. rewrite IHa2. rewrite rename_union. fsetdec.
    - simpl. rewrite IHa. rewrite rename_remove. fsetdec.
Qed.

Lemma rename_fv_fresh: forall rho x a, x `notin` fv a -> rename_var rho x `notin` fv (rename rho a).
Proof.
  intros. unfold not in *.
  intros Fr.
  apply (rename_in rho) in Fr.
  rewrite self_inverse_var in Fr.
  rewrite <- fv_rename in Fr.
  rewrite self_inverse in Fr.
  auto.
Qed.

Lemma rename_fv_fresh2 : forall z x1 a1, z <> x1 -> z `notin` fv a1 -> remove z (fv (rename (x1, z) a1)) [=] remove x1 (fv a1).
Proof.
  intros.
  rewrite fv_rename.
  assert (z0 = (rename_var (x1, z0) x1)). rewrite rename_swap_var. rewrite rename_var_diff. auto. auto.
  replace (remove z0 (rename_set (x1, z0) (fv a1))) with
    (remove (rename_var (x1,z0) x1) (rename_set (x1, z0) (fv a1))).
  rewrite rename_remove.
  simpl.
  assert (M : x1 `notin` (remove x1 (fv a1))). auto.
  apply AtomSetFacts.not_mem_iff in M. rewrite M. simpl.
  assert (N : z0 `notin` (remove x1 (fv a1))). auto.
  apply AtomSetFacts.not_mem_iff in N. rewrite N. fsetdec.
  f_equal. auto.
Qed.
  
  (* -------------------  Naive version of aeq ------------------ *)
  
  Inductive naive_aeq :  forall (a:exp) (b:exp), Prop :=
  | naeq_Var : forall x, naive_aeq (Var x) (Var x) 
  | naeq_App : forall a1 a2 b1 b2,
      naive_aeq a1 a2 -> naive_aeq b1 b2 ->
      naive_aeq (App a1 b1) (App a2 b2)
  | naeq_Abs_diff : forall x1 a1 x2 a2,
      x2 `notin` fv a1 -> naive_aeq a1 (rename (x2, x1) a2) ->
      naive_aeq (Abs x1 a1) (Abs x2 a2)
  | naeq_Abs_same : forall x a1 a2,
      naive_aeq a1 a2 ->
      naive_aeq (Abs x a1) (Abs x a2).

  Hint Constructors naive_aeq.


  
  (* Note:
     In the abs case, just requiring 
       naive_aeq a1 (rename (x2, x1) a2)  
       leads to  \x. y =aeq  \y. x 
     (and the proof of transitivity fails.)

     But, if we just add this to rule out the above: 
      x2 `notin` fv a1 -> naive_aeq a1 (rename (x2, x1) a2)
     then the proof of reflexivity fails. So we also 
     need to have naeq_Abs_same.

     But, x2 `notin` fv a1 only makes it difficult to show that the 
     relation is symmetric. We need to argue that cases like this
     cannot occur.

       \x. x =aeq= \y.x    < note that x1 appears free in a2 >

     Seems tricky.
   *)

  Lemma naeq_rename : forall a b, naive_aeq a b -> forall rho,
        naive_aeq (rename rho a) (rename rho b).
  Proof.
    intros a b H. induction H; intros rho; simpl; auto.
    apply naeq_Abs_diff.
    apply rename_fv_fresh. auto.
    rewrite commute.
    auto.
  Qed.
  
    
  Lemma naeq_refl : forall a, naive_aeq a a.
  Proof. intros a. induction a; auto.
  Qed.

  (* The next two lemmas seem difficult to prove. *)
  
  Lemma naeq_sym : forall a b, naive_aeq a b -> naive_aeq b a.
  Proof. intros a b E. induction E; auto.
         destruct (x2 == x1).
         -  subst. apply naeq_Abs_same. rewrite rename_id in IHE. auto.
         - apply naeq_Abs_diff.
           admit.  (* don't know the symmetric freshness constraint. *)
           apply naeq_rename with (rho := (x2,x1)) in IHE.
           rewrite self_inverse in IHE.
           rewrite rename_swap in IHE.
           auto.
  Admitted.


Lemma naeq_trans : forall a b, naive_aeq a b -> forall c, naive_aeq b c -> naive_aeq a c.
  Proof.
    intros a b E. induction E; intros c E'; auto.
    - inversion E'. subst. auto.
    - inversion E'. subst. admit.
      subst. admit.
Admitted.

  
  Lemma naeq_fv : forall a1 a2, naive_aeq a1 a2 -> fv a1 [=] fv a2.
  Proof.
    intros. induction H.
    - simpl. fsetdec.
    - simpl. fsetdec.
    - simpl. (* now what?? *)
      destruct (x1 == x2).
      + subst. 
        rewrite IHnaive_aeq.
        rewrite rename_id. fsetdec.
      + rewrite IHnaive_aeq. rewrite fv_rename.
      assert (x1 = rename_var (x2,x1) x2). rewrite <- rename_swap_var.
      rewrite rename_var_diff. auto. auto.
      assert (remove x1 (rename_set (x2, x1) (fv a2)) = remove (rename_var (x2,x1) x2) (rename_set (x2, x1) (fv a2))).
      f_equal. auto.
      rewrite H2.
      rewrite rename_remove.
      (* only holds if x1 not free in a2. but we don't know that. *)
      admit.
    -  simpl. rewrite IHnaive_aeq. fsetdec.
  Admitted.

  (*  -------------- Ok, another potential definition of aeq ----------------- *)

  (* This section explores definitions that do not quantify "for all" variables 
     in the case of abstractions. Instead, the in_exp and aeq definitions
     use a premise that requires the relation to hold only for a single, 
     suitably fresh variable. *)
  
  Module ExistsFresh.

    Inductive in_exp (X : atoms) : exp -> Prop :=
    | in_Var : forall x, x `in` X -> in_exp X (Var x)
    | in_App : forall a1 a2, in_exp X a1 -> in_exp X a2 -> in_exp X (App a1 a2)
    | in_Abs : forall z x a1, z `notin` X -> in_exp (X \u {{z}}) (rename (z,x) a1)
                         -> in_exp X (Abs x a1).
    Hint Constructors in_exp.
  
  Check in_exp_ind.

  Lemma in_exp_respects : forall X1  e, in_exp X1 e -> forall X2, X1 [=] X2 -> in_exp X2 e.
  Proof.
    intros X1 e H. induction H; intros X2 EQ; auto.
    apply in_Var. fsetdec.
    apply in_Abs with (z := z0).
    fsetdec.
    apply IHin_exp. fsetdec.
  Qed.


  (* have to prove renaming for *everything* *)
  Lemma in_exp_rename : forall X e, in_exp X e -> forall rho, in_exp (rename_set rho X) (rename rho e).
  Proof.
    intros X e IN.
    induction IN; intros rho.
    - intros. apply rename_in with (rho := rho) in H.
      simpl. auto.
    - intros. simpl in *. auto.
    - intros. simpl in *.
      apply in_Abs with (z := rename_var rho z0).
      + intro Fr.
        unfold not in H.
        apply H. apply rename_in with (rho:= rho) in Fr.
        rewrite self_inverse_var in Fr. rewrite self_inverse_set in Fr. auto.
      + rewrite commute.
        apply in_exp_respects with (X1 := (rename_set rho (union X (singleton z0)))).
        auto.
        rewrite rename_union.
        rewrite rename_singleton.
        fsetdec.
  Qed.

  (* "exists fresh" version of alpha equivalence *)
   
  Inductive aeq : forall X (a:exp) (b:exp), Prop :=
  | aeq_Var : forall X x, x \in X -> aeq X (Var x) (Var x) 
  | aeq_App : forall X a1 a2 b1 b2,
      aeq X a1 a2 -> aeq X b1 b2 ->
      aeq X (App a1 b1) (App a2 b2)
  | aeq_Abs : forall X x1 a1 x2 a2 z,
      z \notin X -> aeq (X \u {{z}}) (rename (x1, z) a1) (rename (x2, z) a2) ->
      aeq X (Abs x1 a1) (Abs x2 a2).
  Hint Constructors aeq.

  Lemma aeq_in : forall X a1 a2, aeq X a1 a2 -> in_exp X a1.
  Proof.
    intros.
    induction H.
    - auto.
    - auto.
    - apply in_Abs with (z := z0). auto.
      rewrite rename_swap. auto.
  Qed.

  Lemma aeq_respects : forall X1 a1 a2, aeq X1 a1 a2 -> forall X2, X1 [=] X2 -> aeq X2 a1 a2.
  Proof.
    intros X1 a1 a2 H. induction H; intros X2 EQ; auto.
    apply aeq_Var. fsetdec.
    apply aeq_Abs with (z := z0). fsetdec.
    apply IHaeq. fsetdec.
  Qed.
    
  Lemma aeq_rename : forall X a b, aeq X a b -> forall rho,
        aeq (rename_set rho X) (rename rho a) (rename rho b).
  Proof.
    intros X a b A. induction A; intros rho.
    - apply rename_in with (rho:=rho) in H. simpl. auto.
    - simpl. auto.
    - simpl. apply aeq_Abs with (z := rename_var rho z0).
      intro Fr. apply H. apply rename_in with (rho := rho) in Fr. rewrite self_inverse_var in Fr. rewrite self_inverse_set in Fr. auto.
      rewrite commute.
      rewrite commute.
      apply aeq_respects with (X1 := rename_set rho (union  X (singleton z0))).
      apply IHA.
      rewrite rename_union. rewrite rename_singleton. fsetdec.
  Qed.

  (* Now these properties are really easy to prove!! *)
  
  Lemma aeq_refl : forall X a, in_exp X a -> aeq X a a.
  Proof. intros X a H. induction H; auto.
         - apply aeq_Abs with (z:= z0).
           auto.
           rewrite rename_swap.  auto.
  Qed.
  Lemma aeq_sym : forall X a b, aeq X a b -> aeq X b a.
  Proof. intros X a b E. induction E; auto.
         - apply aeq_Abs with (z := z0). auto.
           auto.
  Qed.

  (* This one is *much* more difficult though. I don't know how to do it. *)
  
  Lemma aeq_trans : forall X a b, aeq X a b -> forall c, aeq X b c -> aeq X a c.
  Proof.
    intros X a b E. induction E; intros c E'; auto.
    - inversion E'. subst. auto.
    - inversion E'. subst.
      destruct (z0 == z1).
      + subst. apply aeq_Abs with (z := z1). auto. auto.
      + apply aeq_Abs with (z := z0). auto.
        apply IHE.
        apply aeq_rename with (rho := (z0, z1)) in H5.
        (* faking it through here. these admits don't really work because
           we don't know that z0 and z1 are different from x2 and x3 *)
        rewrite <- commute in H5.
        rewrite rename_var_diff in H5.
        assert (rename_var (z0, z1) x2 = x2). admit. rewrite H0 in H5.
        assert (rename (z0,z1) a2 = a2). admit.  rewrite H1 in H5.
        rewrite <- commute in H5.
        rewrite rename_var_diff in H5.
        assert (rename_var (z0, z1) x3 = x3). admit. rewrite H2 in H5.
        assert (rename (z0,z1) a3 = a3). admit.  rewrite H4 in H5.
        apply aeq_respects with (X1 := (rename_set (z0, z1) (union X (singleton z1)))). auto.
        rewrite rename_union.
        assert (rename_set (z0,z1) X = X). admit. rewrite H6.
        rewrite rename_singleton. rewrite rename_var_diff. fsetdec.
        auto. auto. auto.
  Admitted.

  Lemma aeq_fv : forall X a1 a2, aeq X a1 a2 -> fv a1 [=] fv a2.
  Proof.
    intros X a1 a2 H. induction H; simpl; auto. 
    - fsetdec.
    - fsetdec.
    - (* if we knew more about the freshness of z0, we could make 
         progress here. But we don't know how z0 compares to x1 and x2. *)
      rewrite <- rename_fv_fresh2 with (z := z0).
      rewrite <- rename_fv_fresh2 with (z := z0) (a1 := a2).
      rewrite IHaeq.
      fsetdec.
      (* not sure what to do with the rest. *)
  Admitted. 

  End ExistsFresh.

  
  (* ----------------------- in (forall fresh version) -------------------- *)

  (* Ok, here is the version that actually corresponds to PFPL. *)
  
  Inductive in_exp (X : atoms) : exp -> Prop :=
  | in_Var : forall x, x `in` X -> in_exp X (Var x)
  | in_App : forall a1 a2, in_exp X a1 -> in_exp X a2 -> in_exp X (App a1 a2)
  | in_Abs : forall x a1, (forall y, y `notin` X -> in_exp (X \u {{y}}) (rename (x,y) a1)) -> in_exp X (Abs x a1).
  Hint Constructors in_exp.
  
  Check in_exp_ind.

  Lemma in_exp_respects : forall X1  e, in_exp X1 e -> forall X2, X1 [=] X2 -> in_exp X2 e.
  Proof.
    intros X1 e H. induction H; intros X2 EQ; auto.
    apply in_Var. fsetdec.
    apply in_Abs. intros.
    eapply H0. fsetdec.
    fsetdec.
  Qed.
   
  Lemma in_exp_subset : forall X1 a, in_exp X1 a -> forall X2, X1 [<=] X2 -> in_exp X2 a.
  Proof.
    intros X1 a IN. induction IN; intros X2 SUB; auto.
    - apply in_Abs.
      intros y0 Fr.
      apply H0. fsetdec.
      fsetdec.
  Qed.

    
  Lemma exists_renamed : forall y0 X rho, y0 `notin` rename_set rho X ->
                                     exists z, z `notin` X /\ y0 = rename_var rho z.
  Proof.
    intros y0 X rho Fr.
    destruct rho as [x y].
    destruct (x == y). subst. exists y0. rewrite rename_set_id in Fr. rewrite rename_var_id. auto.
    simpl. simpl in Fr.
    destruct (AtomSetProperties.In_dec x X).
    destruct (AtomSetProperties.In_dec y X).
    { destruct (AtomSetFacts.mem_iff X x) as [I _]. rewrite (I i) in Fr.
      destruct (AtomSetFacts.mem_iff X y) as [J _]. rewrite (J i0) in Fr.
      simpl in Fr.
      exists y0. split. auto.
      assert (y0 <> x). fsetdec.
      assert (y0 <> y). fsetdec.
      destruct (y0 == x). contradiction. destruct (y0 == y). contradiction. auto. }
    { destruct (AtomSetFacts.mem_iff X x) as [I _]. rewrite (I i) in Fr.
      destruct (AtomSetFacts.not_mem_iff X y) as [J _]. rewrite (J n0) in Fr.
      simpl in Fr.
      assert (y0 <> y). fsetdec.
      destruct (y0 == x).
      exists y. split. auto. neq_var y x.  eq_var_refl y. auto.
      exists y0. split. fsetdec. neq_var y0 x. neq_var y0 y. auto.
      }
    { destruct (AtomSetProperties.In_dec y X).
      destruct (AtomSetFacts.not_mem_iff X x) as [I _]. rewrite (I n0) in Fr.
      destruct (AtomSetFacts.mem_iff X y) as [J _]. rewrite (J i) in Fr.
      simpl in Fr.
      assert (y0 <> x). fsetdec.
      destruct (y0 == y).
      exists x. split. auto. eq_var_refl x. auto.
      exists y0. split. fsetdec. neq_var y0 x. neq_var y0 y. auto.
      {
        destruct (AtomSetFacts.not_mem_iff X x) as [I _]. rewrite (I n0) in Fr.
        destruct (AtomSetFacts.not_mem_iff X y) as [J _]. rewrite (J n1) in Fr.
        simpl in Fr.
        destruct (y0 == x).
        exists y. split. auto. neq_var y x. eq_var_refl y. auto.
        destruct (y0 == y).
        exists x. split. auto. eq_var_refl x. auto.
        exists y0. split. auto. neq_var y0 x. neq_var y0 y. auto.
      }
    }
  Qed.

  (* have to prove renaming for *everything* *)
  Lemma in_exp_rename : forall X e, in_exp X e -> forall rho, in_exp (rename_set rho X) (rename rho e).
  Proof.
    intros X e IN rho.
    induction IN.
    - intros. apply rename_in with (rho := rho) in H.
      simpl. auto.
    - intros. simpl in *. auto.
    - intros. simpl in *.
      apply in_Abs.
      intros y0 Fr.
      destruct (exists_renamed y0 _ rho Fr) as [y1 [Fry EQ]].
      rewrite EQ.
      rewrite commute.
      eapply in_exp_respects with (X2 := union (rename_set rho X) (singleton y0)) in H0; eauto.
      subst. auto.
      rewrite rename_union.
      rewrite (rename_singleton rho y1).
      rewrite EQ.
      fsetdec.
  Qed.          

 
  
  (* ----------------------- alpha equivalence definition -------------------- *)
  
  Inductive aeq : forall X (a:exp) (b:exp), Prop :=
  | aeq_Var : forall X x, x \in X -> aeq X (Var x) (Var x) 
  | aeq_App : forall X a1 a2 b1 b2,
      aeq X a1 a2 -> aeq X b1 b2 ->
      aeq X (App a1 b1) (App a2 b2)
  | aeq_Abs : forall X x1 a1 x2 a2,
      (forall z, z \notin X -> aeq (X \u {{z}}) (rename (x1, z) a1) (rename (x2, z) a2)) ->
      aeq X (Abs x1 a1) (Abs x2 a2).
  Hint Constructors aeq.

  Lemma aeq_in : forall X a1 a2, aeq X a1 a2 -> in_exp X a1.
  Proof.
    intros.
    induction H.
    - auto.
    - auto.
    - apply in_Abs.
      intros. auto.
  Qed.

  Lemma aeq_respects : forall X1 a1 a2, aeq X1 a1 a2 -> forall X2, X1 [=] X2 -> aeq X2 a1 a2.
  Proof.
    intros X1 a1 a2 H. induction H; intros X2 EQ; auto.
    apply aeq_Var. fsetdec.
    apply aeq_Abs. intros.
    eapply H0. fsetdec.
    fsetdec.
  Qed.
    
  Lemma aeq_rename : forall X a b, aeq X a b -> forall rho,
        aeq (rename_set rho X) (rename rho a) (rename rho b).
  Proof.
    intros X a b A. induction A; intros rho.
    - apply rename_in with (rho:=rho) in H. simpl. auto.
    - simpl. auto.
    - simpl. apply aeq_Abs.
      intros z Fr. replace z with (rename_var rho (rename_var rho z)).
      rewrite commute.
      rewrite commute.
      apply aeq_respects with (X1 := rename_set rho (union  X (singleton (rename_var rho z)))).
      apply H0.
      unfold not.
      unfold not in Fr. intros. apply Fr. apply rename_in with (rho:=rho) in H1.
      rewrite self_inverse_var in H1. auto.
      rewrite rename_union.
      rewrite rename_singleton.
      fsetdec.
      apply self_inverse_var.
  Qed.

  (* Now all three of these properties are really easy to prove!! *)
  
  Lemma aeq_refl : forall X a, in_exp X a -> aeq X a a.
  Proof. intros X a H. induction H; auto.
  Qed.
  Lemma aeq_sym : forall X a b, aeq X a b -> aeq X b a.
  Proof. intros X a b E. induction E; auto.
  Qed.
  Lemma aeq_trans : forall X a b, aeq X a b -> forall c, aeq X b c -> aeq X a c.
  Proof.
    intros X a b E. induction E; intros c E'; auto.
    - inversion E'. subst. auto.
    - inversion E'. subst.
      apply aeq_Abs. intros z Fr.
      apply H0. auto. auto.
  Qed.

  
  Lemma aeq_fv : forall X a1 a2, aeq X a1 a2 -> fv a1 [=] fv a2.
  Proof. 
    intros. induction H.
    - simpl. fsetdec.
    - simpl. fsetdec.
    - simpl.
      pick fresh z for (X \u fv a1 \u fv a2 \u singleton x1 \u singleton x2).
      assert (FX: z `notin` X). auto.
      pose (J := H0 z FX). clearbody J.
      rewrite <- rename_fv_fresh2 with (z := z).
      rewrite <- rename_fv_fresh2 with (z := z)(a1 := a2).
      rewrite J.
      fsetdec.
      auto.
      auto.
      auto.
      auto.
  Qed.

  (* ----------------------------------------- *)

  (* substitution as a relation *)

  Inductive subst (u : exp) (x: atom) : atoms -> exp -> exp -> Prop :=
  | subst_Var_same : forall X , subst u x X (Var x) u
  | subst_Var_diff : forall X y, y `in` X -> x <> y -> subst u x X (Var y) (Var y)
  | subst_App : forall X e1 e1' e2 e2',
      subst u x X e1 e1' -> subst u x X e2 e2' ->
      subst u x X (App e1 e2) (App e1' e2')
  | subst_Abs : forall X e1 e1' y,
      (forall z, z `notin` X ->
            subst u x (X \u {{z}}) (rename (y,z) e1) (rename (y,z) e1')) ->
      subst u x X (Abs y e1) (Abs y e1').
  Hint Constructors subst.
  
  Lemma subst_respects : forall u x X1 e1 e2, subst u x X1 e1 e2 -> forall X2, X1 [=] X2 ->
                                         subst u x X2 e1 e2.
  Proof.
    intros u x X1 e1 e2 H; induction H; intros; auto.
    - apply subst_Var_diff. fsetdec. auto.
    - eapply subst_Abs. intros.
      eapply H0. fsetdec. fsetdec.
  Qed.

  Lemma subst_subset : forall u x X1 e1 e2, subst u x X1 e1 e2 -> forall X2, X1 [<=] X2 ->
                                         subst u x X2 e1 e2.
  Proof.
    intros u x X1 e1 e2 H; induction H; intros; auto.
    - eapply subst_Abs. intros.
      eapply H0. fsetdec. fsetdec.
  Qed.
  
  Lemma subst_in_exp_1 : forall u x X e1 e2, subst u x X e1 e2 -> in_exp (X \u {{x}}) e1.
  Proof.
    intros. induction H; auto.
    - apply in_Abs.
      intros y1 F.
      eapply in_exp_respects with (X1 := (union (union X (singleton y1)) (singleton x0))).
      apply (H0 y1).
      fsetdec.
      fsetdec.
  Qed.

  Lemma subst_in_exp_2 : forall u x X e1 e2, in_exp X u -> subst u x X e1 e2 -> in_exp X e2.
  Proof.
    intros. induction H0; auto.
    - apply in_Abs. intros y1 F.
      eapply (H1 y1). auto.
      eapply in_exp_subset. eauto. fsetdec.
  Qed.


  Lemma subst_function : forall X x u e1, in_exp X e1 -> forall X1, (X1 \u {{x}}) [=] X -> in_exp X1 u -> exists e2, subst u x X1 e1 e2.
  Proof.
    intros X x u e1 I.
    induction I; intros X1 EQ IN.
    - destruct (x0 == x).  subst. exists u. auto.
      exists (Var x0).
      apply subst_Var_diff. fsetdec. auto.
    - destruct (IHI1 X1) as [a1' S1]; auto.
      destruct (IHI2 X1) as [a2' S2]; auto.
      exists (App a1' a2'). auto.
    - pick fresh y for (X1 \u {{x}}).
      destruct (H0 y) with (X1 := (union X1 {{ y }})) as [a1' S1]. fsetdec. fsetdec.
      apply in_exp_subset with (X1 := X1). auto. fsetdec.
      exists (Abs x0 (rename (x0, y) a1')).
      apply subst_Abs.
      intros z0 F.
      rewrite <- commute.
  Admitted.

  Lemma subst_aeq : forall X x u e1 e2, subst u x X e1 e2 -> forall u' e1',
        aeq X u u' -> aeq (X \u {{x}}) e1 e1' -> exists e2', aeq X e2 e2' /\ subst u' x X e1' e2'.
  Proof.
  Admitted. 
