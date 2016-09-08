Require Export Metalib.Metatheory.
Require Export Ch5.

(*************************************************************************)
(** * Preservation 6.2 *)
(*************************************************************************)

(** *** Exercise
    Complete the proof of preservation.  In this proof, we proceed by
    induction on the given typing derivation.  The induction
    hypothesis has already been appropriately generalized by the given
    proof fragment.
    Proof sketch: By induction on the typing derivation for [e].
      - [typing_var] case: Variables don't step.
      - [typing_op] case: By case analysis on how [e] steps.
      - [typing_let] case: The
        [eval_let_red] case is interesting, since it follows by the
        substitution lemma.  The others follow directly from the
        induction hypotheses.
*)

  (* HINTS:
       - Use [auto] and [eauto], especially with [;], to solve
         "uninteresting" subgoals.
       - Use [inversion] to perform case analyses and to rule out
         impossible cases.
       - In the [eval_let_red] subcase of the [typing_let] case:
          -- Use [inversion] on a typing judgement to obtain a
             hypothesis about when the body of the abstraction is
             well-typed.
          -- Use [subst_intro] to rewrite the [open] operation into an
             [open] followed by a [subst].  You'll need to pick a
             fresh variable first.
  *)

Lemma preservation : forall (E : env) e e' T,
  typing E e T ->
  eval e e' ->
  typing E e' T.
Proof.
  intros E e e' T H.
  generalize dependent e'.
  induction H; intros e' J.
(* EXERCISE *) Admitted.

(*************************************************************************)
(** * Progress *)
(*************************************************************************)


 (** *** Exercise
    Complete the proof of the progress lemma.  The induction
    hypothesis has already been appropriately generalized by the given
    proof fragment.
    Proof sketch: By induction on the typing derivation for [e].
      - [typing_var] case: Can't happen; the empty environment doesn't
        bind anything.
      - [typing_let] case: Always reduces.
      - [typing_op] case: always reduces.  The result follows
        from an exhaustive case analysis on whether the two components
        of the operation step or are values and the fact that a
        value must be a nat.
*)

  (* HINTS:
       - Use [auto] and [eauto], especially with [;], to solve
         "uninteresting" subgoals.
       - Use [inversion] to rule out impossible cases.
       - The lemma [typing_to_lc] will be useful for reasoning
         about local closure.
       - In the [typing_op] case:
          -- Use [destruct] to perform a case analysis on the
             conclusions of the induction hypotheses.
          -- Use [inversion] on a [value] judgement to determine that
             the value must be an abstraction.
  *)

Lemma progress : forall e T,
  typing nil e T ->
  value e \/ exists e', eval e e'.
Proof.
  intros e T H.

  (* It will be useful to have a "non-destructed" form of the given
     typing derivation, since [induction] takes apart the derivation
     it is called on. *)
  assert (typing nil e T); auto.

  (* [remember nil as E] fails here because [nil] takes an implicit
     argument that Coq is unable to infer.  By prefixing [nil] with
     [@], we can supply the argument to nil explicitly. *)
  remember (@nil (atom * typ)) as E.

  induction H; subst.

(* FILL IN HERE (and delete "Admitted") *) Admitted.

(*************************************************************************)
(** * Canonical Forms *)
(*************************************************************************)

(** Exercise: The above proof implicitly reasons about the canonical forms 
    of values.  State and prove the canonical forms lemma for this language. 
    (Lemma 6.3). *)

(*************************************************************************)
(** * Run-time errors *)
(*************************************************************************)

(** Challenge Exercise: 

    Add a division operator and an error term (of any type) to this
    language, as described in Section 6.3. You'll want to start a new 
    file from  scratch, starting with the definitions from Section 4. 
*)


