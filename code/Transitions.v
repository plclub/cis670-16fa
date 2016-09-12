
(*************************************************************************)
(** * Transition Systems (PFPL 5.1) *)
(*************************************************************************)

(* The beginning of Ch5 introduces general terminology for reasoning about 
   the evaluation of programs.  We can capture the generality of these 
   definition using Coq's module system. The following module type 
   defines what it means to be a transition system in abstract terms. 
 *)

Module Type TransitionSystem.
  Parameter S : Set.
  Parameter state : S -> Prop.

  Parameter final : S -> Prop.
  Axiom final_state : forall s, final s -> state s.

  Parameter initial : S -> Prop.
  Axiom initial_state : forall s, initial s -> state s.
  
  Parameter step : S -> S -> Prop.
  Axiom step_states : forall s1 s2, step s1 s2 -> state s1 /\ state s2.

  Axiom final_does_not_step : forall s, final s -> not (exists s', step s s').    
  
End TransitionSystem.

(* Once we know what a transition system is, we can define terminolody
   and prove theorems in terms of the basic definitions above. *)

Module TransitionSystemProperties (TS : TransitionSystem).
  Import TS.

  Definition stuck (s : S) :=
    not (final s) /\ not (exists s', step s s').

  (* The multistep relation describes a sequence of transitions. *)
  Inductive multistep : S -> S -> Prop :=
    | ms_refl : forall s, state s -> multistep s s
    | ms_step : forall s s' s'', step s s' -> multistep s' s'' -> multistep s s''.        
  Hint Constructors multistep.
  
  Lemma multistep_transitive : forall s s' s'',
      multistep s s' -> multistep s' s'' -> multistep s s''.
  Proof.
    intros s s' s'' MS1 MS2.
    induction MS1; eauto.
  Qed.

  Lemma multistep_states : forall s1 s2, multistep s1 s2 -> state s1 /\ state s2.
  Proof.
    intros s1 s2 MS. induction MS. auto. split.
    destruct (step_states _ _ H). auto. destruct IHMS. auto.
  Qed.

  (* We say with this is a transition sequence if the first state 
     is initial. *)
  Definition transition_sequence s s' (ms : multistep s s') := initial s.

  (* It is a maximial transition sequence if the last state doesn't step. *)
  Definition maximal_transition_sequence s s' (ms : multistep s s') :=
    initial s /\ not (exists s'', step s' s'').

  (* And a complete transition sequence if the last step is final *)
  Definition complete_transition_sequence s s' (ms : multistep s s') :=
    initial s /\ final s'.
  

End TransitionSystemProperties.  
