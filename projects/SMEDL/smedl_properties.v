(*Here lists some major theorem proved*)

(*Theorem finalIsStuck : forall conf, finalConfig conf -> stuckConfig conf. *)

(* Theorem Terminates: forall conf e (p:stuckConfig conf + ~ stuckConfig conf), initialConfig conf
-> In e (raisedevents conf)
-> ~(generalErrConfig e conf)
->  (exists conf', chainMerge conf conf' e  /\ (stuckConfig conf')).*)

(*
Theorem deterministicMacroStep: forall conf conf1 conf2 n1 n2,
 initialConfig conf  ->
 deter_property conf ->
 noCyclicCausalRelation conf -> 
chainMergeWithEventList conf conf1 n1 ->
chainMergeWithEventList conf conf2 n2 ->
stuckConfig conf1 ->
stuckConfig conf2 ->
equivConf conf1 conf2. 
*)

(*some general lemmas are put here for proving the determinism property*)
(*Once the proof is finished, they will be moved to the helper file*)

Require Import
  Coq.Strings.String
  Coq.Lists.List
  Coq.Bool.Bool
  Coq.Vectors.Vector
  Coq.ZArith.ZArith
  Coq.ZArith.Zdigits
  Coq.QArith.QArith_base
  Coq.QArith.Qabs
  Coq.FSets.FMapList
  Coq.FSets.FMapFacts
  Coq.Init.Notations
  Coq.omega.Omega.

Require Import Coq.Sorting.Permutation.
Require Export SmedlAST_submission.
Require Export SMEDL_helper.
Require Export semantic_rules.

Print In_event_definition.  

Set Implicit Arguments.
Set Boolean Equality Schemes.

Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Require Import Coq.Strings.Ascii.

(*General aux lemmas*)
(*basic aux lemma*)
Lemma termL2: forall conf e lst scs conf', constructConfigList' scs e conf = Result lst /\ 
 In conf' lst -> exists sce, In sce scs /\  Result conf' = constructConfig sce e conf.
Proof.
intros. destruct H.  generalize dependent lst. induction scs.
- intros. simpl in H. induction lst. inversion H0. inversion H.
- intros. induction lst. simpl in H. inversion H0. simpl in H. 
  simpl in H0. destruct H0. remember (constructConfig a e conf ). destruct e0. 
  destruct (constructConfigList' scs e). inversion H;subst. exists a. split. simpl;left. auto. apply Heqe0. inversion H. 
inversion H. simpl. destruct  (constructConfig a e conf ). remember (constructConfigList' scs e conf).
destruct e0. inversion H. rewrite H3 in IHscs. destruct IHscs with lst. auto. auto.  exists x. 
destruct H1. split. right;auto. auto. inversion H. inversion H.
Qed.          


(*basic aux lemma*)
Lemma termL2': forall scs conf e lst  sce, constructConfigList' scs e conf = Result lst ->
 In sce scs -> exists conf', Result conf' = constructConfig sce e conf.
Proof.  intro lst. induction lst.
- intros. inversion H0.
- intros. destruct H0. simpl in H. 
remember (constructConfig a e conf). destruct e0. exists v. rewrite <- H0. auto.
inversion H. simpl in H. 
destruct (constructConfig a e conf). Focus 2. inversion H. 
remember (constructConfigList' lst e conf). destruct e0. eapply IHlst. symmetry. apply Heqe0. auto. inversion H.    
Qed.      

(*basic aux lemma*)
Lemma termL2'': forall scs conf e lst conf'  sce, constructConfigList' scs e conf = Result lst ->
 In sce scs -> Result conf' = constructConfig sce e conf -> In conf' lst.
Proof.  intro lst. induction lst.
- intros. inversion H0.
- intros. destruct H0. simpl in H. 
remember (constructConfig a e conf). destruct e0.  remember (constructConfigList' lst e conf ). 
destruct e0. inversion H. rewrite H0 in Heqe0.  rewrite <- H1 in Heqe0. inversion Heqe0. simpl. left;auto.
inversion H. inversion H. 
simpl in H. destruct (constructConfig a e conf). remember (constructConfigList' lst e conf).
destruct e0. inversion H. simpl. right.   symmetry in Heqe0.  eapply IHlst. apply Heqe0. apply H0. 
auto. inversion H. inversion H.              
   
Qed.      

(*aux lemma to prove sceNoChange *)
Lemma sceNoChange': forall    lst sce sce'  s0, 
sce<>sce' -> 
getScenarioState sce' (lst) =
getScenarioState sce' (updateControlState (lst) sce s0).
Proof. intro lst.  induction lst.
- intros. simpl. auto.
- intros.
simpl. destruct a. destruct (string_dec (scenarioId sce') (scenarioId s)). 
+  unfold updateControlState. simpl. 
destruct (string_dec (scenarioId s) (scenarioId sce)). 
* simpl. unfold not in H. rewrite <- e in e0.       
rewrite ScenarioEquivalence in e0. exfalso. apply H. symmetry;auto.
* simpl. rewrite e.    
destruct (string_dec (scenarioId s) (scenarioId s)). auto. exfalso;apply n0. auto.
+  unfold updateControlState; simpl.
destruct (string_dec (scenarioId s) (scenarioId sce)). 
* simpl. rewrite e. destruct (string_dec (scenarioId sce') (scenarioId sce)).
rewrite ScenarioEquivalence in e0. exfalso. apply H. symmetry;auto.
apply IHlst. auto.
* simpl. destruct (string_dec (scenarioId sce') (scenarioId s)). 
exfalso. apply n. auto. apply IHlst. auto.
Qed.  

(*aux lemma to prove sceNoChangeList *)
Lemma sceNoChange: forall conf conf' sce e, constructConfig sce e conf = Result conf'
-> (forall sce', sce' <> sce /\ In sce (dom (controlstate conf)) -> getScenarioState sce' (  (controlstate conf)) = getScenarioState sce' (  (controlstate conf'))).
Proof.
intros. unfold constructConfig in H. 
destruct (getScenarioState sce (controlstate conf));inversion H;clear H2.
destruct (findEventInstance e (datastate conf) (transEvMap (Some s, Some (eventDefinition e)))); inversion H;clear H2.
destruct (createValueEnv (eventArgs e0) (eventParams (eventDefinition e)) (eventArguments e));inversion H;clear H2.
destruct (valid (extendEnv v (datastate conf)) e0 sce conf);inversion H;clear H2.
destruct (getStep conf sce e0);inversion H;clear H2.
destruct (checkValueNonDeterminism conf e s0);inversion H;clear H2.
unfold configTransition in H. 
destruct (updateDataState (extendEnv v (datastate conf)) (stepActions s0));inversion H;clear H2. 
simpl.  apply sceNoChange'. destruct H0;auto.
Qed. 

(*aux lemma to prove sceNoChangeList'*)
Lemma sceNoChangeList: forall scs sce re conf lst,
incl scs (dom (controlstate conf)) ->
~(In sce scs) -> Result lst = constructConfigList' scs re conf
-> (forall conf', In conf' lst -> getScenarioState sce ((controlstate conf)) = getScenarioState sce ((controlstate conf'))).
Proof.
intros. 
assert (exists sce, In sce scs /\ Result conf' = constructConfig sce re conf).  
SearchAbout constructConfigList. (*first, prove conf' = constructConfig sce re conf and sce' in scs, then sce <> sce' -> ....*)  
pose proof termL2. apply H3 with (lst:=lst). split. symmetry;auto. auto.
destruct H3. eapply sceNoChange. symmetry. destruct H3.  apply e. 
destruct H3. split. Focus 2.           
unfold incl in H. 
apply H in H3. auto.
unfold not;intros. rewrite <- H5 in H3. exfalso;apply H0;auto.
Qed. 

(*basic aux lemma*)
Lemma transformIn': forall  l s conf   re, 
 In s (transformConfig (l) re conf) -> In s (l).
Proof. intro.  induction l.
- intros. simpl in H. inversion H.
- intros. simpl in H. destruct (constructConfig a re conf). inversion H. simpl. left. auto.
simpl. right. apply IHl with (conf:=conf) (re:=re). auto.
destruct (string_dec s0 error3).
simpl. right. apply IHl with (conf:=conf) (re:=re). auto.
simpl in H. destruct H. simpl. left. auto.   
simpl. right.  apply IHl with (conf:=conf) (re:=re).
 auto. 
Qed.

(*aux lemma*)
Lemma sceNoChangeList': forall scs sce re conf lst,
incl scs (dom (controlstate conf)) ->
~(In sce (transformConfig ((filterList (finishedscenarios conf) scs scenario_dec)) re conf  )) -> 
Result lst = constructConfigList  scs re conf
-> (forall conf', In conf' lst -> getScenarioState sce ((controlstate conf)) = getScenarioState sce ((controlstate conf'))).
Proof. intros. apply sceNoChangeList with (scs:=(transformConfig (filterList (finishedscenarios conf) scs scenario_dec) re conf)) (lst:=lst) (re:=re);auto.
apply incl_tran with (m:=scs);auto. 
unfold incl. intros. (*apply filterL2 with (decA:=scenario_dec) .  *)
apply   transformIn' with(conf:=conf) (re:=re) in H3. 
eapply filterL2 with (decA:=scenario_dec). apply H3.
Qed.   

(**)
Lemma mergeControlSceInvariant: forall cso cs1 cs2 cs3 sce, In sce (dom cso) -> (dom cso = dom cs1) -> (dom cs1 = dom cs2)
-> Result cs3 = mergeControlStateFunc cso cs1 cs2 -> getScenarioState sce (cs1) = getScenarioState sce (cs2) -> 
 getScenarioState sce (cs1) = getScenarioState sce (cso)
-> getScenarioState sce (cso) = getScenarioState sce (cs3).
Proof. intro cso. induction cso.
- intros. inversion H.
- intros. simpl in H. destruct H. 

+ simpl. destruct a.   destruct (string_dec (scenarioId sce) (scenarioId s)). 
* simpl in H2. destruct cs1. inversion H2. destruct cs2.  inversion H1.  inversion H1. subst.
inversion H0;subst. simpl. destruct p;destruct p0.  destruct (scenario_dec (fst (s, s1))).
simpl. simpl in H3.  destruct (string_dec (scenarioId s) (scenarioId s)). inversion H0.       
destruct (scenario_dec (fst (s, s1)) s2).  inversion e2.
destruct (mergeControlStateFunc cso cs1 cs2).    
destruct (string_dec s1 s3). inversion H2. simpl.  
destruct (string_dec (scenarioId s) (scenarioId s)).  simpl in H4.
destruct (string_dec (scenarioId s) (scenarioId s)). symmetry;auto.
exfalso;apply n. auto.  exfalso;apply n. auto.  simpl in H4.  
destruct (string_dec s1 s0). inversion H2. simpl.   
destruct (string_dec (scenarioId s) (scenarioId s)). 
destruct (string_dec (scenarioId s) (scenarioId s2)). rewrite e3 in H3. auto.
rewrite <- e2 in n0. simpl in n0. exfalso;apply n0;auto.
exfalso;apply n0;auto. inversion H2. simpl.        
destruct ( string_dec (scenarioId s) (scenarioId s)). symmetry;auto. exfalso;apply n0;auto.
exfalso;apply n1;auto. inversion H2. inversion H2. exfalso;apply n;auto. inversion H2.
* 
rewrite <- H in n. simpl in n. exfalso;apply n;auto.
+ simpl.  destruct a.     destruct (string_dec (scenarioId sce) (scenarioId s)). 
*
simpl in H2. destruct cs1. inversion H2. destruct cs2.  inversion H1.  inversion H1. subst.
inversion H0;subst. simpl. destruct p;destruct p0.  destruct (scenario_dec (fst (s, s1))).
simpl. simpl in H3.  
destruct (scenario_dec (fst (s, s1)) s2).  
destruct (mergeControlStateFunc cso cs1 cs2).    
destruct (string_dec s1 s3). inversion H2. simpl.  
 simpl in H4.
destruct (string_dec (scenarioId sce) (scenarioId s)).  symmetry;auto.
exfalso;apply n. auto.   simpl in H4.
destruct (string_dec s1 s0). inversion H2 . simpl. 
destruct (string_dec (scenarioId sce) (scenarioId s)).  rewrite e0 in e1. 
destruct (string_dec (scenarioId sce) (scenarioId s2)). rewrite e2 in H3. auto.
rewrite <- e1 in n0.   exfalso;apply n0. auto. exfalso;apply n0. auto. 
destruct (string_dec (scenarioId sce) (scenarioId s)). inversion H2. simpl. 
rewrite e2. 
destruct (string_dec (scenarioId s) (scenarioId s)). symmetry. auto.  
exfalso;apply n1.  auto. exfalso;apply n1. auto. inversion H2. inversion H2. inversion H2.

* simpl in H4.   destruct (string_dec (scenarioId sce) (scenarioId s)).
rewrite e in n.   exfalso;apply n;auto. 
simpl in H2. 

destruct cs1. inversion H2. destruct cs2.  inversion H1.  inversion H1. subst.
inversion H0;subst. simpl. destruct p;destruct p0.  destruct (scenario_dec (fst (s, s1)) s).
simpl. simpl in H3.  
destruct (scenario_dec (fst (s, s1)) s2). Focus 2. inversion H2. Focus 2. inversion H2.    
remember (mergeControlStateFunc cso cs1 cs2).
destruct e1.   
destruct (string_dec s1 s3). Focus 3. inversion H2.      inversion H2. simpl.  
 simpl in H4.
destruct (string_dec (scenarioId sce) (scenarioId s)). 
exfalso;apply n. auto.  destruct (string_dec (scenarioId sce) (scenarioId s2) ).
  rewrite e in e0. rewrite <- e0 in e2. exfalso;apply n0.  auto.
apply IHcso with (cs1:=cs1) (cs2:=cs2). auto. auto. auto. auto. auto. auto. 
simpl in H4.  
destruct (string_dec s1 s0). inversion H2. simpl.
destruct (string_dec (scenarioId sce) (scenarioId s)).  exfalso;apply n0.  auto.
 destruct (string_dec (scenarioId sce) (scenarioId s2) ).
  rewrite e in e0. rewrite <- e0 in e2. exfalso;apply n0.  auto.
apply IHcso with (cs1:=cs1) (cs2:=cs2). auto. auto. auto. auto. auto. auto.

     destruct (string_dec (scenarioId sce) (scenarioId s)). exfalso;apply n0.  auto.
 destruct (string_dec (scenarioId sce) (scenarioId s2) ).  rewrite e1 in n3. rewrite e in e0. rewrite e0 in n3.
   exfalso;apply n3.  auto.     
inversion H2. simpl. 
destruct (string_dec (scenarioId sce) (scenarioId s)).   exfalso;apply n0.  auto. 
apply IHcso with (cs1:=cs1) (cs2:=cs2). auto. auto. auto. auto. auto. auto.
  
Qed. 
   


 Lemma mergeControlInvariant: forall cso cs1 cs2 cs3, (dom cso = dom cs1) -> (dom cs1 = dom cs2) 
-> (Result cs3 = mergeControlStateFunc cso cs1 cs2)-> (dom cso) = (dom cs3).
Proof. intros. generalize dependent cso. generalize dependent cs1. generalize dependent cs2. 
induction (cs3). intros. 

 repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. 

destruct (cso). auto. destruct cs1.  inversion H. destruct cs2. inversion H0. simpl in H1.
destruct p;destruct p0;destruct p1.    destruct (scenario_dec s s1).  destruct (scenario_dec s s3).  
destruct (mergeControlStateFunc cso cs1 cs2). destruct (string_dec s2 s4).
destruct (mergeControlStateFunc l cs1 cs2).  inversion H1. inversion H1.   
destruct (mergeControlStateFunc l cs1 cs2). destruct (string_dec s2 s0). inversion H1. inversion H1.
inversion H1.     
destruct (mergeControlStateFunc l cs1 cs2 ). 
 
  destruct (string_dec s2 s4).
inversion H1. 
destruct (string_dec s2 s0). inversion H1.   
 inversion H1. inversion H1.  inversion H1. inversion H1. 
intros.
 repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.  
remember (mergeControlStateFunc cso cs1 cs2).
destruct (e).   
destruct cso;destruct cs1;destruct cs2. 
simpl in Heqe. inversion Heqe. simpl in Heqe. inversion Heqe. simpl in Heqe. inversion Heqe.
simpl in Heqe. inversion Heqe. simpl in Heqe. destruct p.   inversion Heqe. simpl in Heqe. 
destruct p. inversion Heqe. simpl in Heqe. destruct p. destruct p0. inversion Heqe. inversion H. inversion H0.
simpl. subst. rewrite  Heqe in H1. simpl in H1.  destruct p; destruct p0; destruct p1.  subst.  
destruct (scenario_dec s s1).  destruct (scenario_dec s s3).    
 remember (mergeControlStateFunc cso cs1 cs2). 
destruct (e2).   destruct (string_dec s2 s4). inversion H1. simpl. f_equal. rewrite <- H8. apply IHl with (cs1:=cs1) (cs2:=cs2).
auto. auto. 
(*
split;auto. split. auto.*) rewrite <- H8 in Heqe2. auto. 
destruct (string_dec s2 s0).  inversion H1.  simpl. f_equal.  
 rewrite <- H8. apply IHl with (cs1:=cs1) (cs2:=cs2).
(*split;auto. split. auto.*) auto. auto. rewrite <- H8 in Heqe2. auto. 
inversion H1.    simpl. f_equal. rewrite <- H8. apply IHl with (cs1:=cs1) (cs2:=cs2).
(*split;auto. split. *)auto. auto. rewrite <- H8 in Heqe2. auto.
inversion H1. inversion H1. inversion H1. inversion H1.    

        
Qed. 

Lemma mergeControlSceInvariant': forall config config1 config2 config3
 sce, dom (controlstate config) = dom (controlstate config1) ->
dom (controlstate config1) = dom (controlstate config2)->
In sce (dom (controlstate config)) ->
 Result config3 = mergeConfigFunc config config1 config2
-> getScenarioState sce ( (controlstate config1)) = getScenarioState sce ( (controlstate config2)) 
-> getScenarioState sce (( (controlstate config1))) = getScenarioState sce (( (controlstate config)))
-> getScenarioState sce ( (controlstate config)) = getScenarioState sce ( (controlstate config3)).
Proof. intros. 
unfold mergeConfigFunc in H2.
destruct (mergeDataStateFunc (datastate config) (datastate config1) (datastate config2) ).
remember (mergeControlStateFunc (controlstate config) (controlstate config1) (controlstate config2)).
destruct e.  
inversion H2;subst. simpl.    
apply mergeControlSceInvariant with (cs1:=controlstate config1) (cs2:=controlstate config2);auto.

inversion H2. inversion H2.
Qed.    

Lemma correct_config_has_scenario: forall conf, correct_configuration conf -> exists sce,
 In sce (dom (controlstate conf)).
Proof. 
     repeat match goal with
            | _ => progress intros
            | _ => solve [simpl; eauto]
            | [ H: correct_configuration _ |- _ ] => destruct H
            | [ H: ?a <> Datatypes.nil |- _ ] => destruct a; [ try solve[intuition] | clear H ]
            end.
   Qed.

Lemma l': forall e conf, length (raisedevents conf) = O -> ~(In e (raisedevents conf)).
Proof. intros. unfold not. intros.  induction (raisedevents conf). inversion H0. inversion H. Qed.      

Lemma l1: forall conf , (finalConfig conf ->
 (forall re sce, In re (raisedevents conf) -> In sce (dom (controlstate conf)) -> ~ (In sce (finishedscenarios conf)) ->
  findEventInstance re (datastate conf) (transEvMap ((getScenarioState sce (controlstate conf)) , Some (eventDefinition re))) = None)).
Proof. intros. unfold finalConfig in H.   assert (In sce (dom (controlstate conf))  -> transEvMap (getScenarioState sce (controlstate conf), Some (eventDefinition re)) = Datatypes.nil).
destruct H. Focus 2. intros. destruct H. apply H3 in H1. rewrite H1. simpl. auto. auto. intros. 
destruct H3.  apply l' in H0.  inversion H0. auto. apply H3. auto. split. auto. auto.        
Qed. 

(*aux lemma for proving finalIsStuck*)
Lemma transformNil2': forall scs conf re,
correct_configuration conf -> (forall sce, In sce (scs) ->
 constructConfig sce re conf = Error error3)
-> transformConfig (scs) re conf = nil.
Proof. intro. induction (scs).
- intros. simpl. auto.   
- intros.  simpl.  simpl in H0. 
assert (constructConfig a re conf = Error error3).
apply H0. left.  auto. rewrite H1. apply IHl. auto. auto.  
Qed.


Lemma getIn': forall (p:scenario) (scs: scenario_env), 
uniqList (dom (scs)) -> In (p) (dom scs) -> (exists q, Some q = getScenarioState (p) scs).
Proof.
intros. generalize dependent p. 
induction scs.
- intros. inversion H0. 
-  intros. simpl in H0. destruct H0.
+ destruct a. rewrite <- H0. simpl. destruct ( string_dec (scenarioId (s)) (scenarioId (s))).
auto. exists s0. auto. exfalso. apply n. auto.   
+  simpl. destruct a.  assert ( (s = p) \/ ~(s=p)). apply excluded_middle. 
destruct H1. rewrite H1.  destruct (string_dec (scenarioId p) (scenarioId p)). exists s0. 
auto.  exfalso. apply n. auto.
inversion H. subst.   Print getScenarioState. 
destruct (string_dec (scenarioId ( p)) (scenarioId s)).       apply ScenarioEquivalence in e.
rewrite <- e in H1. exfalso. apply H1. auto.   apply IHscs. auto. auto.     
Qed.


(*aux lemma for proving termination*)
Lemma valueConstruction: forall conf e,
(exists x, constructConfigList (dom (controlstate conf)) e conf = Result x)
\/  (exists s : string, constructConfigList (dom (controlstate conf)) e conf = Error s).
Proof. intros.   destruct (constructConfigList (dom (controlstate conf)) e conf).
left. exists v. auto.
right. exists s. auto.
Qed.      


Definition consL (conf conf': configuration) (lst: list configuration) (scs: list scenario) (e: raisedEvent): Prop := 
(In conf' lst -> exists sce, In sce scs /\  Result conf' = constructConfig sce e conf).

(*aux lemma*)
Lemma termL3: forall e conf sce conf',  Result conf' = constructConfig sce e conf  ->
 (finishedscenarios conf' = sce::(finishedscenarios conf)).
Proof. 
intros. unfold constructConfig in H.   
destruct (getScenarioState sce (controlstate conf)). 
destruct (findEventInstance e (datastate conf) (transEvMap (Some s, Some (eventDefinition e)))).  
destruct (createValueEnv (eventArgs e0) (eventParams (eventDefinition e)) (eventArguments e)) .
destruct (valid (extendEnv v (datastate conf)) e0 sce conf).  
destruct (getStep conf sce e0). 
destruct (checkValueNonDeterminism conf e s0).   unfold  configTransition in H.
destruct (updateDataState (extendEnv v (datastate conf)) (stepActions s0)) .
inversion H. simpl. auto. inversion H. inversion H. inversion H. inversion H. inversion H. inversion H.
inversion H. 
Qed.           

(*aux lemma*)
Lemma termL3': forall e conf sce conf',  Result conf' = constructConfig sce e conf  ->
 (forall sce', In sce' (finishedscenarios conf) ->In sce'  (finishedscenarios conf')).
Proof. 
intros. pose proof termL3. 
assert (finishedscenarios conf' = sce :: finishedscenarios conf).  
eapply H1. apply H. rewrite H2. simpl; right;auto.  
Qed.

(*aux lemma*)
Lemma finishedInvariant: forall e conf lst scs sce, constructConfigList' scs e conf = Result lst
(*-> In sce scs*) -> In sce (finishedscenarios conf) 
-> (forall conf', In conf' lst -> In sce (finishedscenarios conf')).
Proof. intros. pose proof termL2'. pose proof termL3'. pose proof termL2.
assert (constructConfigList' scs e conf = Result lst /\ In conf' lst).
split;auto. apply H4 in H5. destruct H5.  destruct H5. 
eapply H3 in H6. apply H6. auto.      
Qed.

(*aux lemma*)
Lemma finishedSceInvariant: forall config config1 config2 config3
 sce, In sce (dom (controlstate config)) -> 
(In sce (finishedscenarios config1) \/
In sce (finishedscenarios config2)) ->
 Result config3 = mergeConfigFunc config config1 config2
-> In sce (finishedscenarios config3) .
Proof. intros.
unfold mergeConfigFunc in H1.     
destruct (mergeDataStateFunc (datastate config) (datastate config1) (datastate config2)).
destruct (mergeControlStateFunc (controlstate config) (controlstate config1) (controlstate config2)).
inversion H1. simpl. unfold  mergeList'.
apply in_or_app. destruct H0. left. auto. 
assert (In sce (finishedscenarios config1) \/ ~(In sce (finishedscenarios config1))).
apply excluded_middle.  destruct H2. left. auto.     right.
SearchAbout filterIn. apply filterIn. auto. auto. inversion H1. inversion H1.    
Qed.
 
 (*aux lemma*)
Lemma finishedInvariantCombine: forall lst conf conf'  sce ,
correct_configuration conf -> In sce (finishedscenarios conf) ->
innerCombineFunc' conf None lst= Result conf' ->
(forall conf', In conf' lst -> In sce (finishedscenarios conf'))
-> In sce (finishedscenarios conf').
Proof. intro lst. induction lst.
- intros. simpl in H1. inversion H1.
-intros. simpl in H1. destruct lst. 
+ simpl in H1. apply H2. inversion H1. simpl;left;auto.
+ simpl in H1.  
remember ( innerCombineFunc' conf (Some c) lst ).
destruct e.   
assert (conf'=a \/ ~(conf'=a)). 
apply excluded_middle. destruct H3.
apply H2. rewrite H3. simpl;left;auto. Focus 2. inversion H1.
assert (In sce (finishedscenarios v)).
 
apply IHlst with (conf:=conf). auto. auto. symmetry;auto. 
intros. apply H2. simpl;right;auto.
eapply finishedSceInvariant. Focus 2. right. apply H4. Focus 2. symmetry. apply H1.
destruct H.
 unfold scenarioInclusion in inclusion. unfold incl in inclusion. apply inclusion. auto.
Qed.                     


Lemma finishedInvariantSync: forall e conf conf' sce, 
correct_configuration conf -> synchrony conf conf' e -> 
In sce (finishedscenarios conf)
-> In sce (finishedscenarios conf').
Proof. intros. unfold synchrony in H0.  
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
unfold combineFunc in H4.
destruct (checkType conf e).
remember (constructConfigList (dom (controlstate conf)) e conf).
destruct e0. destruct v. inversion H4.       
eapply finishedInvariantCombine. apply H. auto. apply H4. intros.
pose proof finishedInvariant. symmetry in Heqe0. unfold constructConfigList in Heqe0.
eapply H6. apply Heqe0. auto. auto. inversion H4. inversion H4.    
Qed. 


Lemma transformIn: forall  l s conf  l3 re, 
correct_configuration conf -> In re (raisedevents conf)
-> s::l3 = transformConfig (l) re conf -> In s (l).
Proof. intro. induction l.
- intros. simpl in H1. inversion H1.
- intros. simpl in H1. destruct (constructConfig a re conf). inversion H1. simpl. left. auto.
destruct (string_dec s0 error3). 
 simpl. right.  apply IHl with (l3:=l3) (conf:=conf) (re:=re). auto. auto. auto.
simpl. left. inversion H1. auto. 
Qed.

(*aux lemma for proving termination*)
Lemma termL23:  forall conf e lst scs conf', constructConfigList scs e conf = Result lst /\ 
 In conf' lst -> exists sce, In sce scs /\ (finishedscenarios conf' = sce::(finishedscenarios conf)).
Proof. intros.   apply termL2 in H. destruct H. exists x. destruct H.   split.  Focus 2. 

apply termL3 with e. auto. 
pose proof transformIn'. apply H1 in H.  
 eapply filterL2 in H.  auto.  
   Qed.  


Local Close Scope Z_scope.
Local Close Scope N_scope.
Local Close Scope Q_scope.
(*aux lemma for proving termination*)
Lemma termL40': forall l1 l2, length (l1) <=
length (mergeList' (l1) (l2) scenario_dec).
Proof. intros.  generalize dependent l0.   induction l2.
intros.  simpl. omega.
intros. simpl.  
assert (forall (A:Type) (l l1: list A), Datatypes.length (l1) <= Datatypes.length ((l1) ++ l)).
intros. induction l3. simpl. omega. simpl. omega. destruct H with (A:=scenario) (l1:=l2) (l:=filterList (a :: l2) l0 scenario_dec).
 omega. omega. 
Qed.


(*aux lemma for proving termination*)
Lemma termL41': forall v0 v conf conf', innerCombineFunc' conf (Some v0) v = Result conf'
-> (Datatypes.length (finishedscenarios v0) <= Datatypes.length (finishedscenarios conf')).
Proof. intros. generalize dependent v0. generalize dependent conf'.     induction v.
intros.  simpl in H. inversion H.  rewrite <- H1. omega.
intros. 
simpl in H.
remember (innerCombineFunc' conf (Some a) v ).
destruct e.  unfold mergeConfigFunc in H. 
destruct (mergeDataStateFunc (datastate conf) (datastate v0) (datastate v1)).
destruct (mergeControlStateFunc (controlstate conf) (controlstate v0) (controlstate v1)).
inversion H. simpl. apply termL40'. inversion H. inversion H. inversion H.       
Qed. 

        
(*aux lemma for proving termination*)
Lemma termL4: forall conf conf' e, synchrony conf conf' e ->
length (finishedscenarios conf) < length (finishedscenarios conf').
Proof. 
intros.  
repeat match goal with
            | [|- forall _,_]  => progress intros
            | [ |-  _  /\  _  ] =>  split
            | [ H: synchrony _ _ _ |- _ ] => unfold synchrony in H

            | [ H: _ /\ _ |- _ ] => destruct H
            | _ => unfold equivConf
end.    
unfold combineFunc in H2.  
remember (constructConfigList (dom (controlstate conf)) e conf).
destruct e0. destruct (checkType conf e).   destruct v. inversion H2. Focus 2. inversion H2.
simpl in H2.      
assert (Datatypes.length (finishedscenarios conf) < Datatypes.length (finishedscenarios c)).
assert (In c (c::v)). simpl. left. auto. assert ((constructConfigList (dom (controlstate conf)) e conf = Result (c :: v)) /\ In c (c :: v) ).
split. auto. auto. 
 apply termL23 in H4. 
destruct H4. destruct H4. rewrite H5. simpl. omega.   
assert (Datatypes.length (finishedscenarios c) <= Datatypes.length (finishedscenarios conf')).
destruct v. simpl in H2.  inversion H2. rewrite <- H5. omega.
apply termL41' with (conf:=conf) (v:=c0::v). auto.
omega.    destruct (checkType conf e). inversion H2. inversion H2.   

Qed. 


Lemma sceFinished: forall conf sce, In sce (finishedscenarios conf) -> In_scenario sce (finishedscenarios conf)= true.
Proof. intros. induction (finishedscenarios conf). inversion H.
simpl. 
 destruct (scenario_dec sce a). auto.
apply IHl. simpl in H. destruct H. Focus 2. auto. rewrite H in n. unfold not in n. exfalso. apply n. auto. Qed.         
           

Lemma LL1': forall conf conf' sce re, constructConfig sce re conf = Result (conf') -> 
~ In sce (finishedscenarios conf) /\  dom (controlstate conf) = (dom (controlstate conf')) /\  (finishedscenarios conf' = sce::(finishedscenarios conf)).
Proof. intros.
split. Focus 2. split. Focus 2.    apply termL3 with re. symmetry. auto.
unfold constructConfig in H.
destruct (getScenarioState sce (controlstate conf)).
destruct (findEventInstance re (datastate conf) (transEvMap (Some s, Some (eventDefinition re)))).
destruct (createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re)).
destruct (valid (extendEnv v (datastate conf)) e sce conf).
destruct (getStep conf sce e ).
destruct (checkValueNonDeterminism conf re s0). 
 unfold configTransition in H.  
destruct (updateDataState (extendEnv v (datastate conf)) (stepActions s0) ).
inversion H. simpl.

assert (forall s1, dom s1 = dom (updateScenarioState' sce (pro_state s0) s1)).
intros. induction s1. simpl.
Print updateScenarioState'.

simpl. auto.
  destruct a. simpl. 
destruct ( string_dec (scenarioId s2) (scenarioId sce)). simpl.  f_equal. auto. simpl. f_equal. auto.
apply H0. 
inversion H. inversion H. inversion H. inversion H. inversion H. inversion H. inversion H.
unfold not; intros. 
unfold constructConfig in H. 
destruct (getScenarioState sce (controlstate conf)).
destruct (findEventInstance re (datastate conf) (transEvMap (Some s, Some (eventDefinition re)))).
destruct (createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re)).
unfold valid in H.  
assert (In_scenario sce (finishedscenarios conf)= true). apply sceFinished. auto.  
 
destruct (getStep conf sce e). 
destruct (      In_event_definition (event (stepEvent s0))
        (map (fun re : raisedEvent => eventDefinition re) (raisedevents conf))).
destruct (evalCondition (extendEnv v (datastate conf)) s0 conf).  
rewrite H1 in H. simpl in H. inversion H. rewrite H1 in H. simpl in H. inversion H. rewrite H1 in H. 
destruct (evalCondition (extendEnv v (datastate conf)) s0 conf). simpl in H. inversion H.
simpl in H.  inversion H. inversion H. inversion H. inversion H. inversion H.        
 
Qed. 

 

(*aux lemma for proving termination*)
Lemma sceInclusion: forall conf, uniqList (dom (controlstate conf)) -> uniqList  (finishedscenarios conf) 
-> scenarioInclusion conf-> 
 length (dom (controlstate conf)) >= length ( (finishedscenarios conf)).
Proof. intros.  apply listInclusion. split. auto. split. auto. unfold scenarioInclusion in H1.  auto.
Qed.        

Lemma domMergeConfig1: forall v v1 v2,  (exists v3, Result (v3) = 
mergeControlStateFunc (v) (v1) (v2)) ->
 dom v = dom v1.
Proof.  
Print mergeControlStateFunc. intro v. 
induction v.
intros. destruct H. inversion H.
intros. destruct H.       
simpl in H.  
remember v. remember v1. remember v2.
destruct s. destruct s0. destruct a. inversion H.  
destruct a.   inversion H. 
 destruct a. destruct p.  destruct s0. inversion H.   
destruct p.           
destruct (scenario_dec s1 s3). 
destruct (scenario_dec s1 s5).
simpl. rewrite e. f_equal. apply IHv with s0. Focus 2. inversion H. Focus 2. inversion H.
    
remember (mergeControlStateFunc l s s0).
destruct e1. exists v0. auto. inversion H.               
Qed. 

Lemma domMergeConfig2: forall v v1 v2,  (exists v3, Result (v3) = 
mergeControlStateFunc (v) (v1) (v2)) ->
 dom v = dom v2.
Proof.  
Print mergeControlStateFunc. intro v. 
induction v.
intros. destruct H. inversion H.
intros. destruct H.       
simpl in H.  
remember v. remember v1. remember v2.
destruct s. destruct s0. destruct a. inversion H.  
destruct a.   inversion H. 
 destruct a. destruct p.  destruct s0. inversion H.   
destruct p.           
destruct (scenario_dec s1 s3). 
destruct (scenario_dec s1 s5).
simpl. rewrite e. f_equal.  rewrite e in e0. auto.   apply IHv with s. Focus 2. inversion H. Focus 2. inversion H.
    
remember (mergeControlStateFunc l s s0).
destruct e1. exists v0. auto. inversion H.               
Qed. 

Lemma domMergeConfig: forall v v1 v2,  (exists v3, Result (v3) = 
mergeControlStateFunc (v) (v1) (v2)) ->
 dom v = dom v1 /\ dom v = dom v2.
Proof. intros. split. apply domMergeConfig1 with v2. auto.
     apply domMergeConfig2 with v1. auto.
Qed. 

Lemma domMergeData1: forall v v1 v2,  (exists v3, Result (v3) = 
mergeDataStateFunc (v) (v1) (v2)) ->
 dom v = dom v1.
Proof.   
 intro v. 
induction v.
-
intros. destruct H. simpl. simpl in H.   inversion H.
-
intros. destruct H.       
simpl in H.  
remember v. remember v1. remember v2.
destruct a. destruct p. destruct v0. inversion H.  
destruct v3. destruct p. destruct p.  inversion H.  
destruct p. destruct p.  destruct p0. destruct p.            
destruct (atom_eq_dec a a0).
destruct (atom_eq_dec a a1).
destruct (typ_eq_dec t t0). 
destruct (typ_eq_dec t t1). 
subst. simpl. f_equal. remember ( mergeDataStateFunc v v0 v3 ).
destruct e. Focus 2. inversion H. 
   eapply IHv. exists v1. apply Heqe. inversion H. inversion H. inversion H. inversion H.                       
Qed. 

Lemma domMergeData2: forall v v1 v2,  (exists v3, Result (v3) = 
mergeDataStateFunc (v) (v1) (v2)) ->
 dom v = dom v2.
Proof.   
 intro v. 
induction v.
-
intros. destruct H. simpl. simpl in H.   inversion H.
-
intros. destruct H.       
simpl in H.  
remember v. remember v1. remember v2.
destruct a. destruct p. destruct v0. inversion H.  
destruct v3. destruct p. destruct p.  inversion H.  
destruct p. destruct p.  destruct p0. destruct p.            
destruct (atom_eq_dec a a0).
destruct (atom_eq_dec a a1).
destruct (typ_eq_dec t t0). 
destruct (typ_eq_dec t t1). 
subst. simpl. f_equal. auto. remember ( mergeDataStateFunc v v0 v3 ).
destruct e. Focus 2. inversion H. 
   eapply IHv. exists v1. apply Heqe. inversion H. inversion H. inversion H. inversion H.                       
Qed. 

Lemma domMergeDataConfig: forall v v1 v2,  (exists v3, Result (v3) = 
mergeDataStateFunc (v) (v1) (v2)) ->
 dom v = dom v1 /\ dom v = dom v2.
Proof. intros. split. apply domMergeData1 with v2. auto.
     apply domMergeData2 with v1. auto.
Qed. 


Lemma domDataMerge: forall  originconf conf' conf'',  (exists rconf,  Result (rconf) = mergeDataStateFunc originconf conf' conf'')
-> (dom ( originconf)) = (dom ( conf')) /\ (dom ( originconf)) = (dom ( conf'')).
Proof.   intros. apply domMergeDataConfig. auto. 
Qed.

Lemma domDataMerge': forall  originconf conf' conf'',  (exists rconf,  Result (rconf) = mergeConfigFunc originconf conf' conf'')
-> (dom (datastate originconf)) = (dom (datastate conf')) /\ (dom (datastate originconf)) = (dom (datastate conf'')).
Proof.   intros. destruct H. unfold mergeConfigFunc in H.
remember (mergeDataStateFunc (datastate originconf) (datastate conf') (datastate conf'')). 
apply domMergeDataConfig. destruct e. Focus 2. inversion H.     exists v. auto.   
    
Qed.


Lemma domMerge: forall  originconf conf' conf'',  (exists rconf,  Result (rconf) = mergeControlStateFunc originconf conf' conf'')
-> (dom ( originconf)) = (dom ( conf')) /\ (dom ( originconf)) = (dom ( conf'')).
Proof.   intros. apply domMergeConfig. auto. 
Qed.

Lemma domMerge': forall  originconf conf' conf'',  (exists rconf,  Result (rconf) = mergeConfigFunc originconf conf' conf'')
-> (dom (controlstate originconf)) = (dom (controlstate conf')) /\ (dom (controlstate originconf)) = (dom (controlstate conf'')).
Proof.   intros. destruct H. unfold mergeConfigFunc in H.
destruct (mergeDataStateFunc (datastate originconf) (datastate conf') (datastate conf'') ).
Focus 2. inversion H.
remember (mergeControlStateFunc (controlstate originconf) (controlstate conf') (controlstate conf'')).
destruct e. 
apply    domMerge. exists v0. auto. inversion H.      
Qed.


Lemma mergeControlSceInvariant'': forall confList config  conf'' sce, 
Result conf'' = innerCombineFunc' config (None) confList -> In sce (dom (controlstate config)) 
-> (forall conf' , (In conf' confList)
-> getScenarioState sce ( (controlstate conf')) = getScenarioState sce ( (controlstate config)))
-> getScenarioState sce ( (controlstate conf'')) = getScenarioState sce ( (controlstate config)).

Proof. intro confList. induction confList.
- intros. simpl in H. inversion H. 
- intros. simpl in H. destruct confList.
+  simpl in H. inversion H. eapply H1. simpl. left;auto.   
+   simpl in H.         
remember  (innerCombineFunc' config (Some c) confList).  
destruct e.  Focus 2. inversion H. assert (getScenarioState sce (controlstate v) = getScenarioState sce (controlstate config)).
apply IHconfList. auto. auto. intros. apply H1. right. auto. 
symmetry. apply mergeControlSceInvariant' with (config1:=a) (config2:=v).        
Focus 4. auto. Focus 4. assert (getScenarioState sce (controlstate a) = getScenarioState sce (controlstate config)).
apply H1. left. auto. rewrite <- H2 in H3. auto. Focus 3. auto. Focus 3. apply H1. left. auto.
pose proof  domMerge'. destruct H3 with (originconf := config) (conf':=a) (conf'':=v). exists conf''. auto. auto. 
 pose proof  domMerge'. destruct H3 with (originconf := config) (conf':=a) (conf'':=v). exists conf''.
auto. rewrite H4 in H5;auto.
Qed. 


Lemma syncSceInvariant:  forall conf conf' e sce,
synchrony conf conf' e -> ~(In sce (transformConfig ((filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) e conf  )) -> 
 In sce (dom (controlstate conf)) -> getScenarioState sce ((controlstate conf)) = getScenarioState sce ((controlstate conf')).
Proof.
intros. unfold synchrony in H. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
unfold combineFunc in H4. 
destruct (checkType conf e).
remember (constructConfigList (dom (controlstate conf)) e conf). 
destruct (e0).
destruct v. inversion H4.   
symmetry in H4. 
Check sceNoChangeList'. symmetry. apply mergeControlSceInvariant'' with (confList:=(c::v)). auto.
auto. intros. Focus 2. inversion H4. Focus 2. inversion H4.
destruct H5.    
 apply sceNoChangeList' with (conf':=c) (lst:=c::v) in H0. symmetry in H0. rewrite <- H5. auto.
 apply incl_refl. auto.  simpl;left;auto.   apply sceNoChangeList' with (conf':=conf'0) (lst:=c::v) in H0. 
symmetry. auto. apply incl_refl. auto. right. auto.
Qed. 
            

Lemma L60: forall rconf originconf conf' conf'',   Result (rconf) = mergeConfigFunc originconf conf' conf'' 
-> (dom (controlstate rconf)) = (dom (controlstate conf')).
Proof. intros.  assert ((dom (controlstate originconf)) = (dom (controlstate conf')) /\ (dom (controlstate originconf)) = (dom (controlstate conf''))).
apply domMerge'. exists rconf. auto. destruct H0.     

unfold mergeConfigFunc in H.  
destruct (mergeDataStateFunc (datastate originconf) (datastate conf') (datastate conf'') ). 
 remember (mergeControlStateFunc (controlstate originconf) (controlstate conf') (controlstate conf'')).
Check mergeControlInvariant. 
destruct e.
apply   mergeControlInvariant in Heqe. simpl in H.  Focus 2. auto. Focus 2. auto. inversion H. simpl. rewrite H0 in H1. auto.
inversion H. simpl. rewrite <- Heqe. auto.

 inversion H. inversion H.    
Qed. 

(*aux lemma for proving determinism*)
Lemma mergeDataStateUniqInvariant': forall l x v0 v,
dom l = dom x ->
dom l = dom v0 ->
Result v = mergeDataStateFunc l x v0
-> dom v = dom l.
Proof.  intro l. induction l.
- simpl. intros. inversion H1.
- simpl. intros.    
destruct a. destruct p.   
destruct x. inversion H1. 
destruct p;destruct p. destruct v0. inversion H1.
destruct p;destruct p. 
destruct (atom_eq_dec a a0). Focus 2. inversion H1. 
destruct (atom_eq_dec a a1). Focus 2. inversion H1.
destruct (typ_eq_dec t t0). Focus 2. inversion H1. 
destruct (typ_eq_dec t t1). Focus 2. inversion H1. 
remember (mergeDataStateFunc l x v0).
destruct e3. Focus 2. inversion H1.    
destruct (range_typ_dec r0 r1).
inversion H1.
Focus 2.     
destruct ( range_typ_dec r0 r ).
Focus 2. simpl. 
inversion H1. simpl. f_equal. eapply IHl.
 simpl in H. inversion H. apply H5.   inversion H0. apply H5. apply Heqe3. 
auto.
simpl. 
inversion H0. 
simpl. f_equal. inversion H1. simpl. f_equal;auto.        
eapply IHl.
 inversion H. apply H7.  apply H4. apply Heqe3. simpl. f_equal;auto.    
eapply IHl.
 inversion H. apply H5.   simpl in H0.  inversion H0. apply H5. auto.  
Qed.   

(*aux lemma for proving determinism*)
Lemma mergeDataStateUniqInvariant: forall l x v0 v,
uniqList (dom l) ->
dom l = dom x ->
dom l = dom v0 ->
Result v = mergeDataStateFunc l x v0
-> uniqList (dom v).
Proof.  intros. assert (dom v = dom l). eapply mergeDataStateUniqInvariant'. apply H0. 
apply H1. auto. subst. rewrite H3. auto.     
Qed.    

(*aux lemma for proving determinism*)
Lemma mergeConfigDomDataInvariant: forall rconf originconf conf' conf'',   Result (rconf) = mergeConfigFunc originconf conf' conf'' 
-> (dom (datastate rconf)) = (dom (datastate conf')).
Proof. 
intros.  assert ((dom (datastate originconf)) = (dom (datastate conf')) /\ (dom (datastate originconf)) = (dom (datastate conf''))).
apply domDataMerge'. exists rconf. auto. destruct H0.     

unfold mergeConfigFunc in H.
remember  (mergeDataStateFunc (datastate originconf) (datastate conf') (datastate conf'') ).
destruct e. Focus 2. inversion H.     
destruct (mergeControlStateFunc (controlstate originconf) (controlstate conf') (controlstate conf'') ).
Focus 2. inversion H. inversion H. simpl.      
apply   mergeDataStateUniqInvariant' in Heqe. subst. rewrite H0 in Heqe;auto.
   simpl in H.  Focus 2. auto.  auto. 
Qed. 


Lemma domControlSyncL1: forall e conf sce conf',   In sce (dom (controlstate conf)) 
-> correct_configuration conf  -> Result conf' = constructConfig sce e conf  -> 
 (dom (controlstate conf)) = (dom (controlstate conf')).
Proof. intros. 
SearchAbout constructConfig.
symmetry in H1. apply LL1' in H1. destruct H1.
destruct H2. auto.
Qed.     

(*aux lemma for proving domControlSync*)
Lemma domControlSyncL4: forall v conf  e  w, correct_configuration conf ->  
(forall conf', In conf' v -> (exists sce, In sce (dom (controlstate conf)) /\  Result (conf')=  constructConfig sce e conf ))
-> Result(w) =  innerCombineFunc' conf None v ->  (dom (controlstate conf)) = (dom (controlstate w)).
Proof. intro v. induction v.
- intros. simpl in H1. inversion H1.
- intros. simpl in H1.   destruct v. simpl in H1.  
inversion H1.  simpl in H0.  destruct H0 with a.  left. auto. destruct H2.
apply domControlSyncL1 with (e:=e) (sce:=x). auto. auto. auto.
simpl in H1.  
remember (innerCombineFunc' conf (Some c) v ).
destruct e0. 
assert ((dom (controlstate conf)) = (dom (controlstate a)) /\ (dom (controlstate conf)) = (dom (controlstate v0))).
apply domMerge'. exists w. auto.    
apply L60 in H1. destruct H2. rewrite H1. auto. inversion H1.     

Qed. 

(*aux lemma for proving termination*)
Lemma domControlSync: forall conf conf' e, correct_configuration conf -> synchrony conf conf' e ->  (dom (controlstate conf)) = (dom (controlstate conf')).
Proof. intros.   
unfold synchrony in H0. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.

unfold combineFunc in H3.   
remember (constructConfigList (dom (controlstate conf)) e conf).
destruct (checkType conf e). 
destruct e0. destruct v. inversion H3.

Focus 2. inversion H3. symmetry in H3.  apply domControlSyncL4 with (e:=e) (v:=(c :: v)) (conf:=conf).
auto. intros. 
unfold constructConfigList in Heqe0. 
inversion H4. remember (transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)).
remember (l e conf). destruct l0. simpl in Heqe0. inversion Heqe0.
simpl in Heqe0.   
remember (constructConfig s e conf). destruct e0. destruct (constructConfigList' l0 e conf). 
inversion Heqe0. subst. exists s. split. Focus 2. rewrite H7.  auto. Focus 2. inversion Heqe0. Focus 2. inversion Heqe0. 
Print transformConfig. 
   simpl in H3. assert (In s (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)).
apply transformIn with (l3:=l0) (re:=e) (conf:=conf).
auto. auto. auto. apply filterL2 in H5. auto. 
Check termL2. pose proof termL2. 
assert (constructConfigList' (transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec) e conf) e conf = Result (c::v) /\ In conf'0 (c::v)).
split. symmetry. auto. auto. apply H6 in H7. destruct H7.  
exists x. split. Focus 2. destruct H7. auto. 
destruct H7. apply transformIn' in H7.
apply filterL2 with (decA:=scenario_dec) (l1:=(finishedscenarios conf)). auto.
auto. inversion H3.  
Qed.



(*aux lemma for proving incluSyncL4*)
Lemma incluSyncL1: forall e conf sce conf',   In sce (dom (controlstate conf)) -> correct_configuration conf  -> Result conf' = constructConfig sce e conf  -> 
scenarioInclusion conf'.
Proof. intros. destruct H0.  unfold scenarioInclusion. unfold scenarioInclusion in inclusion.
symmetry in H1. apply LL1' in H1. destruct H1. destruct H1.  rewrite H2. rewrite <- H1.  apply inclInvariant. auto. 
auto. auto.
Qed.   
          
(*aux lemma for proving incluSyncL4*)
Lemma incluSyncL2: forall rconf originconf conf' conf'',   Result (rconf) = mergeConfigFunc originconf conf' conf'' 
/\ scenarioInclusion originconf /\ scenarioInclusion conf' /\ scenarioInclusion conf'' -> scenarioInclusion rconf.

Proof.  intros. destruct H. remember H. clear Heqe.    
apply L60 in H. assert ( (dom (controlstate originconf)) = (dom (controlstate conf')) /\ (dom (controlstate originconf)) = (dom (controlstate conf''))). 
 apply domMerge'. exists rconf. auto.     
 
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H
            end.

unfold  scenarioInclusion.
rewrite H.     
unfold mergeConfigFunc in e. 
destruct ( mergeDataStateFunc (datastate originconf)
        (datastate conf') (datastate conf'')).
remember (mergeControlStateFunc (controlstate originconf) (controlstate conf') (controlstate conf'')). 
destruct e0.  
destruct (mergeControlStateFunc (controlstate originconf) (controlstate conf') (controlstate conf'')).
Focus 2. inversion Heqe0. Focus 2.   inversion e.

destruct (mergeList' (raisedevents conf') (raisedevents conf'') raisedEvent_dec). 
destruct (mergeList' (exportedevents conf') (exportedevents conf'') raisedEvent_dec).
inversion e. simpl. 
apply mergeInclu. unfold scenarioInclusion in H3.  auto. rewrite  H1 in H2. rewrite H2.  unfold scenarioInclusion in H4. auto.
inversion e. 
simpl.  apply mergeInclu. unfold scenarioInclusion in H3. auto. rewrite  H1 in H2. rewrite H2.  unfold scenarioInclusion in H4. auto.
inversion e. simpl. 
  apply mergeInclu. unfold scenarioInclusion in H3. auto. rewrite  H1 in H2. rewrite H2.  unfold scenarioInclusion in H4. auto.
inversion e. 

Qed.  


(*aux lemma for proving incluSync*)
Lemma incluSyncL4: forall v conf e  w, correct_configuration conf ->  
(forall conf', In conf' v -> (exists sce, In sce (dom (controlstate conf)) /\  Result (conf')=  constructConfig sce e conf ))
-> Result(w) =  innerCombineFunc' conf None v -> scenarioInclusion w.
Proof. intro v. induction v.
- intros. simpl in H1. inversion H1.
- intros. simpl in H1.  destruct v. simpl in H1. 
inversion H1. simpl in H0. destruct H0 with a. left. auto. 
apply incluSyncL1 with (e:=e) (sce:=x) (conf:=conf). destruct H2.
auto. auto. destruct H2. auto.
simpl in H1.
remember (innerCombineFunc' conf (Some c) v ).
destruct e0.  
assert (scenarioInclusion v0). apply IHv with (conf:=conf) (e:=e). auto. intros. 
apply H0. simpl in H2. destruct H2. simpl. right.  left. auto. simpl. right. right. auto.
simpl. auto.   

assert ( Result w = mergeConfigFunc conf a v0 /\ scenarioInclusion conf /\ scenarioInclusion a /\ scenarioInclusion v0).
split. auto. split. destruct H. auto. split.  
assert (exists sce : scenario, In sce (dom (controlstate conf)) /\ Result a = constructConfig sce e conf).
apply H0. simpl. left. auto. 
destruct H3.  
apply incluSyncL1 with (e:=e) (sce:=x) (conf:=conf).  destruct H3. auto. auto. destruct H3. auto.
auto.      
  apply  incluSyncL2 in H3. auto.  inversion H1.   

Qed. 
  
(*aux lemma for proving termL5*)
Lemma incluSync: forall conf conf' e,  correct_configuration conf -> synchrony conf conf' e -> scenarioInclusion conf'.
Proof. intros.   
unfold synchrony in H0. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.

unfold combineFunc in H3.
destruct (checkType conf e).    
remember (constructConfigList (dom (controlstate conf)) e conf).
destruct e0. destruct v. inversion H3.

Focus 2. inversion H3. symmetry in H3.  apply incluSyncL4 with (e:=e) (v:=(c :: v)) (conf:=conf).
auto. intros. Focus 2. auto.
unfold constructConfigList in Heqe0.   
inversion H4. remember (transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)).
remember (l e conf). destruct l0. simpl in Heqe0. inversion Heqe0.
simpl in Heqe0.   
remember (constructConfig s e conf). destruct e0. destruct (constructConfigList' l0 e conf). 
inversion Heqe0. subst. exists s. split. Focus 2. rewrite H7.  auto. Focus 2. inversion Heqe0. Focus 2. inversion Heqe0. 
Print transformConfig. 
   simpl in H3. assert (In s (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)).
apply transformIn with (l3:=l0) (re:=e) (conf:=conf).
auto. auto. auto. apply filterL2 in H5. auto. 
Check termL2. pose proof termL2. 
assert (constructConfigList' (transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec) e conf) e conf = Result (c::v) /\ In conf'0 (c::v)).
split. symmetry. auto. auto. apply H6 in H7. destruct H7.  
exists x. split. Focus 2. destruct H7. auto. 
destruct H7. apply transformIn' in H7.
apply filterL2 with (decA:=scenario_dec) (l1:=(finishedscenarios conf)). auto.
inversion H3. 
Qed.



Lemma uniqSyncL1: forall e conf sce conf',   In sce (dom (controlstate conf)) -> correct_configuration conf  -> Result conf' = constructConfig sce e conf  -> 
uniqList (dom (controlstate conf')) 
/\ uniqList (finishedscenarios conf').
Proof.  intros. assert (dom (controlstate conf) = dom (controlstate conf')).
symmetry in H1. apply LL1' in H1. destruct H1.
destruct H2.  auto.
destruct H0. split. rewrite <- H2. auto.
symmetry in H1. apply LL1' in H1. 
destruct H1. destruct H1. rewrite H3. SearchAbout   uniqList.  apply uniqL_push.
auto. auto.
Qed.    
           
  
  
Lemma uniqSyncL2: forall rconf originconf conf' conf'', correct_configuration originconf
-> uniqList (dom (controlstate conf')) 
-> uniqList (finishedscenarios conf') 
-> uniqList (dom (controlstate conf'')) 
-> uniqList (finishedscenarios conf'') 
->  Result (rconf) = mergeConfigFunc originconf conf' conf'' 
 -> uniqList (dom (controlstate rconf)) 
/\ uniqList (finishedscenarios rconf).
Proof. intros.
split.
- assert ( dom (controlstate originconf) = dom (controlstate conf') /\
       dom (controlstate originconf) = dom (controlstate conf'')). 
apply     domMerge'. exists rconf. auto. 

assert ((dom (controlstate rconf) = (dom (controlstate conf')))).
apply L60 with (originconf:=originconf) (conf'':=conf'').
auto. destruct H5. rewrite <- H5 in H6.
rewrite H6. destruct H. auto.
- unfold mergeConfigFunc in H4.           
destruct (mergeDataStateFunc (datastate originconf) (datastate conf') (datastate conf'')).
destruct (mergeControlStateFunc (controlstate originconf) (controlstate conf') (controlstate conf'')).
inversion H4. simpl. 
SearchAbout mergeList'.    
Focus 2. inversion H4. Focus 2. inversion H4.
apply uniqMerge. auto. auto.
Qed.   
     
Lemma uniqSyncL3: forall v conf e  w, correct_configuration conf ->  
(forall conf', In conf' v -> (exists sce, In sce (dom (controlstate conf)) /\  Result (conf')=  constructConfig sce e conf ))
-> Result(w) =  innerCombineFunc' conf None v ->  uniqList (dom (controlstate w)) 
/\ uniqList (finishedscenarios w).
Proof. 
intro v. induction v.
- intros. simpl in H1. inversion H1.
- intros. simpl in H1.  destruct v. simpl in H1. 
inversion H1. simpl in H0. destruct H0 with a. left. auto. 
apply uniqSyncL1 with (e:=e) (sce:=x) (conf:=conf). destruct H2.
auto. auto. destruct H2. auto.
simpl in H1.
remember (innerCombineFunc' conf (Some c) v ).
destruct e0.  
apply uniqSyncL2 in H1. auto. auto.  
assert (uniqList (dom (controlstate a)) /\ uniqList (finishedscenarios a)).
destruct H0 with a. simpl. left.  auto.
apply uniqSyncL1 with (e:=e) (sce:=x) (conf:=conf); destruct H2;
auto; auto; destruct H2; auto; destruct H2; auto.
destruct H2. auto.
assert (uniqList (dom (controlstate a)) /\ uniqList (finishedscenarios a)).
destruct H0 with a. simpl. left.  auto.
apply uniqSyncL1 with (e:=e) (sce:=x) (conf:=conf); destruct H2;
auto; auto; destruct H2; auto; destruct H2; auto.
destruct H2. auto.
simpl in IHv.  
assert (uniqList (dom (controlstate v0)) /\ uniqList (finishedscenarios v0)).
apply IHv with (conf:=conf) (e:=e). auto. intros. 
apply H0. destruct H2. simpl. right. left. auto. simpl. right. right. auto.
auto. destruct H2. auto.             
assert (uniqList (dom (controlstate v0)) /\ uniqList (finishedscenarios v0)).
apply IHv with (conf:=conf) (e:=e). auto. intros. 
apply H0. destruct H2. simpl. right. left. auto. simpl. right. right. auto.
simpl. auto. destruct H2. auto. inversion Heqe0. inversion H1.    
Qed. 


Lemma uniqSync: forall conf conf' e,  correct_configuration conf -> synchrony conf conf' e -> uniqList (dom (controlstate conf')) 
/\ uniqList (finishedscenarios conf').
Proof.  intros.   
unfold synchrony in H0. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.

unfold combineFunc in H3. unfold constructConfigList in H3.
destruct (checkType conf e). 
remember (constructConfigList' (transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec) e conf) e conf).
destruct e0. destruct v. inversion H3.   

Focus 2. inversion H3. symmetry in H3.  apply uniqSyncL3 with (e:=e) (v:=(c :: v)) (conf:=conf).
auto. intros. 
inversion H4. remember (transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)).
remember (l e conf). destruct l0. simpl in Heqe0. inversion Heqe0.
simpl in Heqe0.   
remember (constructConfig s e conf). destruct e0. destruct (constructConfigList' l0 e conf). 
inversion Heqe0. subst. exists s. split. Focus 2. rewrite H7.  auto. Focus 2. inversion Heqe0. Focus 2. inversion Heqe0. 
Focus 3. auto.
Print transformConfig. 
   simpl in H3. assert (In s (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)).
apply transformIn with (l3:=l0) (re:=e) (conf:=conf).
auto. auto. auto. apply filterL2 in H5. auto. 
Check termL2. pose proof termL2. 
assert (constructConfigList' (transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec) e conf) e conf = Result (c::v) /\ In conf'0 (c::v)).
split. symmetry. auto. auto. apply H6 in H7. destruct H7.  
exists x. split. Focus 2. destruct H7. auto. 
destruct H7. apply transformIn' in H7.
apply filterL2 with (decA:=scenario_dec) (l1:=(finishedscenarios conf)). auto.
inversion H3. 
Qed. 


Lemma scenarioStateNotNone: forall l sce, In sce (dom l) -> getScenarioState sce l <> None.
Proof. intros. induction (l). 
- inversion H.
- simpl. destruct a.   
destruct (string_dec (scenarioId sce) (scenarioId s)).
unfold not;intros. inversion H0. apply IHl0. simpl in H. 
destruct H. rewrite H in n. exfalso. apply n. auto. auto.
Qed.      
   
(*a correct configuration will step to a correct configuration*)
(*used to prove termination and determinism*)
Lemma termL5: forall conf conf' e, correct_configuration conf -> synchrony conf conf' e
-> correct_configuration conf'.
Proof. intros. remember H. clear Heqc.
destruct H. split. 
SearchAbout uniq. 
Check domControlSync.
pose proof domControlSync.  
assert (dom (controlstate conf) = dom (controlstate conf')).
eapply H. auto. apply H0.

 rewrite <-  H1. auto.
Focus 2.  pose proof uniqSync.
assert (uniqList (dom (controlstate conf')) /\ uniqList (finishedscenarios conf')).
apply H with (conf:=conf) (e:=e);auto. destruct H1;auto.
Focus 2.  pose proof uniqSync. assert (uniqList (dom (controlstate conf')) /\ uniqList (finishedscenarios conf')).
apply H with (conf:=conf) (e:=e);auto. destruct H1;auto.  
Focus 2.  pose proof incluSync. apply H with (conf:=conf) (e:=e);auto.
intros.   apply scenarioStateNotNone. auto. 
Qed.




(*begin proof of finalIsStuck*)
(*aux lemma for proving finalIsStuck*)
Lemma finalNoStep1: forall conf re ,  finalConfig conf  ->  In re (raisedevents conf) ->
  ~(exists lst,  lst<> nil /\ Result lst = constructConfigList (dom (controlstate conf)) re conf).
Proof. intros. unfold not. intros. remember H0. clear Heqi.  
destruct H1. destruct H1. unfold constructConfigList in H2. 
assert ((transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec) re conf) = nil).
unfold finalConfig in H.  
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
destruct H3. assert  ((raisedevents conf) = nil). induction (raisedevents conf). auto. inversion H3. 
  rewrite H4 in H0.
inversion H0.
apply H3 in H0.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. 
apply transformNil2'.
auto. intros. 
  unfold constructConfig. 
Print correct_configuration.
remember H5. clear Heqi0.  
 apply filterL1 with (l2:=dom (controlstate conf)) (decA:=scenario_dec) in H5.
Check filterL2. 
apply filterL2 in i0.
assert (transEvMap (getScenarioState sce (controlstate conf), Some (eventDefinition re)) = Datatypes.nil).
pose proof getIn'. destruct H. 
apply H4. split. auto. auto. destruct H.
pose proof getIn'.   
apply H with (p:=sce) in cs_dom_uniq.  destruct cs_dom_uniq.
rewrite <- H7. rewrite <- H7 in H6.  rewrite H6. simpl. auto. auto.   
rewrite H3 in H2. simpl in H2. inversion H2. apply H1. auto.
Qed. 


(*aux lemma for proving finalIsStuck*)
Lemma finalNoStep1'': forall conf re, 
 ~(exists lst,  lst<> nil /\ Result lst = constructConfigList (dom (controlstate conf)) re conf)
->~(exists conf', combineFunc  re  conf = Result conf').
Proof. intros. unfold not.  intros.
unfold not in H. apply H. destruct H0.
unfold combineFunc in H0.
destruct (checkType conf re). 
remember (constructConfigList (dom (controlstate conf)) re conf).
destruct e. destruct v. inversion H0.

exists (c::v). split. intros. inversion H1. auto.
 inversion H0. inversion H0.
Qed.                   

(*aux lemma for proving finalIsStuck*)
Lemma finalNoStep: forall conf re ,  finalConfig conf  ->  In re (raisedevents conf) ->
  ~(exists conf',  (synchrony conf conf' re)).
Proof.  intros. pose proof finalNoStep1''.
pose proof  finalNoStep1.
apply H2 with (re:=re) in H.  apply H1 in H.
Focus 2.
auto.  unfold not; intros. destruct H3. unfold synchrony in H3. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
exfalso. apply H. exists x. auto.
Qed.        

    
(*final configuration is stuck configuration*)
Theorem finalIsStuck : forall conf, finalConfig conf -> stuckConfig conf. 
Proof. intros. unfold stuckConfig. intros. apply finalNoStep. auto. auto. Qed.     

(*end proof of finalIsStuck*)


(*begin main proof of termination*)

(*upperbound of number of steps to the final configuration*)
Definition UpperBound (conf:configuration): nat :=
length (dom (controlstate conf)) - length (finishedscenarios conf).

Print stuckConfig. 
(*upperbound of number of steps to the final configuration*)
(*if the configuration is stuck, the upperbound is 0.*)
Definition UpperBound' (conf:configuration) (p: (stuckConfig conf) + ~(stuckConfig conf) ) : nat := 
match p with
| inl p' => O
| inr p' => length (dom (controlstate conf)) - length (finishedscenarios conf)
end. 

Check UpperBound'.


Lemma decrease': forall a b c, a > 0 /\ b >=0 /\ c>=0 /\  a>=b /\ a>=c /\ c < b -> a-b < a-c.
Proof. intros.    

   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
omega.
Qed.   

(*after each micro-step, the upperbound is reduced*)
Lemma decrease: forall conf conf' e, 
correct_configuration conf -> synchrony conf conf' e -> UpperBound conf' <   UpperBound conf.
Proof. intros.  remember H0. remember H0. remember H0. clear Heqs1.     clear Heqs. clear Heqs0.    apply termL4 in H0.   apply domControlSync in s.  
unfold   UpperBound.  Focus 2.  auto. rewrite s. apply decrease'.  split.   destruct H. 
destruct ( dom (controlstate conf)). unfold not in cs_non_empty. exfalso. apply cs_non_empty. auto.
rewrite <- s. simpl. auto. omega. 
split. omega. 
split. omega. 
split. Focus 2. split. Focus 2. auto. 
rewrite <- s.  

apply sceInclusion; destruct H; auto; auto. apply incluSync in s0.     apply sceInclusion.   
Focus 3. auto. Focus 3. destruct H. auto. apply uniqSync in s1; destruct s1; auto.
split;auto. split;auto.   
apply uniqSync in s1; destruct s1; auto.
apply uniqSync in s1; destruct s1; auto.
Qed.   

(*after each micro-step, the upperbound is reduced*)
Lemma decrease'': forall conf conf' e (p1: (stuckConfig conf) + ~(stuckConfig conf) )  (p2:(stuckConfig conf') + ~(stuckConfig conf')), 
correct_configuration conf -> synchrony conf conf' e -> @UpperBound' conf'  p2 <   @UpperBound' conf  p1.
Proof. intros. destruct p1. simpl.  
unfold stuckConfig in s. 
destruct s with e. unfold synchrony in H0.
destruct H0. auto. exists conf'. auto.
destruct p2. simpl.  
apply decrease in H0. unfold UpperBound in H0. omega. auto.
simpl. apply decrease with e. auto. auto.   
Qed.   

Lemma combineConstruction: forall conf e,
(exists conf' : configuration, Result conf' = combineFunc e conf) \/ ((exists s, Error s = combineFunc e conf)). 

Proof. intros.   destruct (combineFunc e conf).
left. exists v. auto.
right. exists s. auto.
Qed.  

Print ErrConfig. 

Definition generalErrConfig e conf : Prop:= 
 (ErrConfig e conf ) \/  (conflict e conf) \/ (exists s, combineFunc e conf = Error (s)). 

Lemma combineFuncDisjunction: forall e conf, ((exists s : string, combineFunc e conf = Error s))
 \/(exists conf' : configuration, combineFunc e conf = Result conf').
Proof. intros.   destruct (combineFunc e conf). right;exists v;auto. left;exists s;auto.
Qed.    

(*a configuration will either step or raise error when applying the synchrony rule*)
Lemma stepOrError: forall conf e, initialConfig conf 
-> In e (raisedevents conf) -> (generalErrConfig e conf) \/ (~(generalErrConfig e conf)
-> exists conf',
synchrony conf conf' e).
Proof. 
intros. destruct H.     
 repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
remember H0. 
clear Heqi. 
apply H2 in H0. 
destruct H0.  
destruct H4.
destruct H4.  
Print constructConfigList. 
assert ((exists lst, constructConfigList (dom (controlstate conf)) (e) conf = Result lst ) \/ ~(exists lst, constructConfigList (dom (controlstate conf)) (e) conf = Result lst )).
apply excluded_middle.
destruct H6. Focus 2. 
left. unfold generalErrConfig. left.  

 unfold ErrConfig. 
intros.   
assert ((exists x, constructConfigList (dom (controlstate conf)) e conf = Result x)
\/  (exists s : string, constructConfigList (dom (controlstate conf)) e conf = Error s)). 
apply valueConstruction.  destruct H8.
unfold not in H6. exfalso. apply H6. auto. auto.
(*unfold generalErrConfig. unfold ErrConfig. left. intros. auto.*)
right. intros. destruct H6.

Print synchrony. Print generalErrConfig.  assert (exists conf',  combineFunc e conf = Result conf').
Print  combineFunc. destruct x0. 
unfold generalErrConfig in H7. assert (exists s : string, combineFunc e conf = Error s).
Print combineFunc.  unfold combineFunc. destruct (checkType conf e).  
exists error9.  rewrite H6. auto. exists error10. auto.  unfold not in H7. 
exfalso. apply H7. right. right. auto. 
Print combineFunc. Print generalErrConfig.

unfold not in H7. unfold  generalErrConfig in H7. 
pose proof combineFuncDisjunction. destruct H8 with (e:=e) (conf:=conf). destruct H9. exfalso. apply H7. 
right. right. exists x1. auto. auto.       
 unfold synchrony. destruct H8. exists x1.
     split. auto. split. unfold not; intros. unfold  not in H7. apply H7. 
unfold generalErrConfig. left. auto. split. 
unfold  not in H7.  unfold not. intros.  apply H7. 
unfold generalErrConfig. right. left. auto. auto.           
                            
Qed. 

(*used to prove the termination*)
Axiom StrongInd :
  forall P: nat -> Prop,
    P 0 ->
    (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
    (forall n, P n).


(*if upperbound is greater than 0 and no error, then it can step forward*)
Lemma NonZeroCanStep: forall conf e (p1: (stuckConfig conf) + ~(stuckConfig conf) ),
In e (raisedevents conf) /\ correct_configuration conf -> @UpperBound' conf p1 > 0 -> ~ generalErrConfig e conf  -> exists conf', synchrony conf conf' e.
Proof. intros. destruct p1. 

simpl in H0. inversion H0.
unfold generalErrConfig in H1.  
assert (~conflict e conf /\  (exists conf', combineFunc e conf = Result conf')).
split. unfold not. intros. unfold not in H1. apply H1. right. left. auto.
unfold not in H1.     
assert ((exists conf' : configuration, Result conf' = combineFunc e conf) \/ ((exists s, Error s = combineFunc e conf))).
apply  combineConstruction. destruct H2. destruct H2. exists x. symmetry. auto. exfalso. apply H1. right. right.
destruct H2. exists x. symmetry. auto.            


destruct H2. destruct H3.   
assert (synchrony conf x e). unfold synchrony . split.      
simpl in H0.      destruct H.    auto. split. Focus 2. split. auto. auto.
unfold not.  intros. unfold not in H1. apply H1. left. auto.
exists x. auto.
Qed.



(*if upperbound is greater than 0 and no error, then it can step forward*)
Lemma NonZeroCanStep': forall conf e ,
In e (raisedevents conf) /\ correct_configuration conf  -> ~ generalErrConfig e conf  -> exists conf', synchrony conf conf' e.
Proof. intros. 
unfold generalErrConfig in H0.  
assert (~conflict e conf /\  (exists conf', combineFunc e conf = Result conf')).
split. unfold not. intros. unfold not in H0. apply H0. right. left. auto.
unfold not in H0.     
assert ((exists conf' : configuration, Result conf' = combineFunc e conf) \/ ((exists s, Error s = combineFunc e conf))).
apply  combineConstruction. destruct H1. destruct H1. exists x. symmetry. auto. exfalso. apply H0. right. right.
destruct H1. exists x. symmetry. auto.            

destruct H1. destruct H2.   
assert (synchrony conf x e). unfold synchrony . split.      
    destruct H.    auto. split. Focus 2. split. auto. auto.
unfold not.  intros. unfold not in H0. apply H0. left. auto.
exists x. auto. 
Qed.

(*aux lemma, if two unique list l1 and l2 have the same length and l1 is included in l2, then l2 is included in l1*)
Lemma revIncl: forall (A: Type) (l1 l2:list A),
incl l1 l2 -> uniqList (l1) -> uniqList (l2) -> length l1 = length l2
-> incl l2 l1.
Proof. intros.
assert (forall (A:Type)  (l:list A), NoDup l <-> uniqList l).
intros. split.
intros. induction l.  inversion H3. Print  uniqList. apply uniqL_nilL.
     Print  uniqList. apply uniqL_push. apply IHl. inversion H3.
auto. inversion H3. auto. intros.
induction l. apply NoDup_nil. apply NoDup_cons.
inversion H3. auto. apply IHl. inversion H3. auto.           
apply NoDup_length_incl.
Focus 2. omega. Focus 2. auto.
destruct H3 with (A:=A) (l:=l2). apply H5. auto.
Qed. 


(*if all state machines finishes execution, configuration is stuck*)
Lemma conditionNotStep: forall conf, 
 correct_configuration conf 
-> Datatypes.length (dom (controlstate conf)) - Datatypes.length (finishedscenarios conf) = 0 
-> stuckConfig conf.  
Proof.  
intros. unfold stuckConfig. intros. unfold not. intros.
destruct H2.   
destruct H. unfold synchrony in H2.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.   
unfold scenarioInclusion in inclusion.
 assert (incl (dom (controlstate conf)) (finishedscenarios conf)).
apply revIncl; auto. 
assert (Datatypes.length (dom (controlstate conf)) >=
     Datatypes.length (finishedscenarios conf)).
apply sceInclusion. auto. auto. auto.      
omega. 
 unfold combineFunc in H4. destruct  (checkType conf e). 
unfold constructConfigList in H4. 
remember (transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)).
remember (l e conf). destruct l0. simpl in H4. inversion H4.
remember (constructConfigList' (s :: l0) e conf). destruct e0. destruct v. inversion H4. 
assert (exists sce : scenario, In sce (dom (controlstate conf)) /\ Result c = constructConfig sce e conf).
simpl in Heqe0. remember ( constructConfig s e conf). destruct e0. destruct (constructConfigList' l0 e conf).
inversion Heqe0. subst. exists s. split. apply transformIn in Heql0. eapply filterL2.  apply Heql0. split;auto. auto. auto.
inversion Heqe0. inversion Heqe0.   destruct H6. destruct H6.               
unfold constructConfig in H7.
destruct (getScenarioState x0 (controlstate conf)).
destruct (findEventInstance e (datastate conf) (transEvMap (Some s0, Some (eventDefinition e)))).
destruct (createValueEnv (eventArgs e0) (eventParams (eventDefinition e)) (eventArguments e)).
unfold valid in H7.  destruct ( getStep conf x0 e0).
destruct ( In_event_definition (event (stepEvent s1))
         (map (fun re : raisedEvent => eventDefinition re) (raisedevents conf))).
destruct ( evalCondition (extendEnv v0 (datastate conf)) s1 conf). 
unfold incl in H5. apply H5 in H6. 
Print In_scenario.   
assert (In_scenario x0 (finishedscenarios conf) = true).
 SearchAbout  In_scenario.   
apply sceFinished.  auto. rewrite H8 in H7. simpl in H7. inversion H7.  
destruct  (eqb (In_scenario x0 (finishedscenarios conf)) false). simpl in H7. inversion H7.
simpl in H7. inversion H7. destruct (eqb (In_scenario x0 (finishedscenarios conf)) false); 
destruct ( evalCondition (extendEnv v0 (datastate conf)) s1 conf). simpl in H7.
inversion H7. simpl in H7. inversion H7. simpl in H7. inversion H7. simpl in H7.
 inversion H7. inversion H7. inversion H7. inversion H7. inversion H7. inversion H4.
inversion H4. 
Qed.                     

(*when upperbound is zero, it is stuck*)
Lemma ZeroIsFinal: forall conf   (p: (stuckConfig conf) + ~(stuckConfig conf) ),  
 correct_configuration conf -> @UpperBound' conf p = O -> stuckConfig conf.
Proof. 
intros.
destruct p. auto. simpl in H0.  unfold stuckConfig.
intros. apply conditionNotStep in H0. unfold not in n. exfalso. apply n.  auto.
auto.     
Qed.

(*error or stuck is decidable*)
Axiom Error_dec : forall conf e, { generalErrConfig e conf } + { ~ generalErrConfig e conf }.                  
Axiom stuckConfig_dec: forall conf', {stuckConfig conf'} + {~ stuckConfig conf'}.
Check stuckConfig_dec.


(*first define termination on this relation*)
Inductive Connected : configuration -> configuration -> raisedEvent -> Prop :=
| ConnectedRefl: forall a e, Connected a a e
| ConnectedTrans: forall a1 a2 a3 e e', synchrony  a1 a2 e -> Connected a2 a3  e' -> Connected a1 a3 e.

Require Import Omega.
Check generalErrConfig. 


Lemma inGenErr': forall conf (a:raisedEvent) l,
 ~ (forall x0, In x0 (a :: l) ->  generalErrConfig x0 conf ) -> generalErrConfig a conf 
 -> ~ (forall x0, In x0 l ->generalErrConfig x0 conf). 
Proof. intros. unfold not in H. unfold not. intros.
apply H. intros. simpl in H2. destruct H2. rewrite <- H2. auto. apply H1.
auto. 
Qed.  

Lemma inGenErr: forall conf,
 ~(forall x0, In x0 (raisedevents conf) -> generalErrConfig x0 conf) ->
exists e', In e' (raisedevents conf) /\ ~(generalErrConfig e' conf).
Proof.
intros. induction (raisedevents conf).
unfold not in H.   exfalso. apply H.  intros.   inversion H0.
pose proof Error_dec conf a. 
destruct H0.
apply inGenErr' with (l:=l)  in g. apply IHl in g. destruct g. exists x. 
split. destruct H0. simpl. right. auto. destruct H0.  auto. auto. auto.       
exists a. split. simpl. left. auto. auto.      
Qed. 
                  

(*termination on connected*)
Lemma TerminatesOnConnected: forall a e, 
correct_configuration a
-> In e (raisedevents a)
-> ~(generalErrConfig e a)
-> exists a',  Connected a a' e /\  (stuckConfig a' \/ (forall e', In e' (raisedevents a') -> (generalErrConfig e' a'))).
Proof.
intros. 
pose proof stuckConfig_dec a.
destruct H2. exists a. split. apply ConnectedRefl. left. auto.    
remember (@UpperBound'  a (inr n)) as mes. 
 revert dependent a. generalize dependent e. 
  induction mes using StrongInd; intros.

  - eauto using ConnectedRefl, ZeroIsFinal.
  - pose proof (NonZeroCanStep). 

assert (exists conf', synchrony a conf' e).
apply H3 with (inr n). split;auto. destruct H0. 
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
omega. auto. destruct H4.
pose proof stuckConfig_dec x.
destruct H5. exists x. split. apply ConnectedTrans with (a2:=x) (e':=e). auto. apply ConnectedRefl.
left. auto. remember H4. clear Heqs.    apply decrease'' with (p1:=inr n) (p2:=inr n0)  in H4. 
remember (UpperBound' (inr n0)). Focus 2. auto.  
rewrite <-  Heqmes in H4. assert (n1<=mes). omega. 
assert (~(raisedevents x = nil)). unfold not. intros. unfold not in n0. apply  n0.
unfold stuckConfig. intros. rewrite H6 in H7. inversion H7. 

assert ((forall x0, In x0 (raisedevents x) -> generalErrConfig  x0 x) \/ ~(forall x0, In x0 (raisedevents x) -> (generalErrConfig x0 x))).

apply excluded_middle. destruct H7. exists x. split. 
assert (exists e', In e' (raisedevents x)). destruct (raisedevents x). unfold not in H6. exfalso. apply H6. auto.
exists r. simpl. left. auto. destruct H8. apply ConnectedTrans with (a2:=x) (e':=x0).
auto. apply ConnectedRefl. right. auto. assert (exists e', In e' (raisedevents x) /\ ~(generalErrConfig e' x)).
apply inGenErr. auto. 
 
unfold not in H7. remember (raisedevents x). induction l. unfold not in H6. exfalso. apply H6. auto.
 destruct H8. destruct H8.    
           apply H with (a:=x) (n:=n0) (e:=x0) in H5.
destruct H5. destruct H5. remember H5. clear Heqc.   exists x1. split. apply ConnectedTrans with (a2:=x) (e':=x0). auto. auto.
auto.  apply termL5 with (conf:=a) (e:=e). auto. auto.
auto. 
generalize dependent x0. unfold not in n0.   
unfold stuckConfig in n0.   
unfold not. intros. rewrite Heql in H8. auto. auto. auto.   
Qed. 

(* all pending events will lead to an error, it is stuck *)
Lemma errorStuck: forall a', (forall e', In e' (raisedevents a') -> (generalErrConfig e' a'))
-> stuckConfig a'.
Proof.
intros. unfold stuckConfig;unfold not;intros.
destruct H1. 
apply H in H0. 
unfold synchrony in H1. unfold generalErrConfig in H0.
destruct H0.
- destruct H1. destruct H2. exfalso;apply H2. auto.
- destruct H0.
+  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
exfalso;apply H3;auto.
+   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
destruct H0. rewrite H4 in H0. inversion H0.
Qed.         

(*termination on connected*)
Lemma TerminatesOnConnected': forall a e, 
correct_configuration a
-> In e (raisedevents a)
-> ~(generalErrConfig e a)
-> exists a',  Connected a a' e /\  (stuckConfig a').
Proof.
intros. 
pose proof stuckConfig_dec a.
destruct H2. exists a. split. apply ConnectedRefl.  auto.    
remember (@UpperBound'  a (inr n)) as mes. 
 revert dependent a. generalize dependent e. 
  induction mes using StrongInd; intros.

  - eauto using ConnectedRefl, ZeroIsFinal.
  - pose proof (NonZeroCanStep'). 

assert (exists conf', synchrony a conf' e).
apply H3 . split;auto. destruct H0. auto.
  destruct H4.
pose proof stuckConfig_dec x.
destruct H5. exists x. split. apply ConnectedTrans with (a2:=x) (e':=e). auto. apply ConnectedRefl.
 auto. remember H4. clear Heqs.    apply decrease'' with (p1:=inr n) (p2:=inr n0)  in H4. 
remember (UpperBound' (inr n0)). Focus 2. auto.  
rewrite <-  Heqmes in H4. assert (n1<=mes). omega.  
assert (~(raisedevents x = nil)). unfold not. intros. unfold not in n0. apply  n0.
unfold stuckConfig. intros. rewrite H6 in H7. inversion H7. 

assert ((forall x0, In x0 (raisedevents x) -> generalErrConfig  x0 x) \/ ~(forall x0, In x0 (raisedevents x) -> (generalErrConfig x0 x))).

apply excluded_middle. destruct H7. exists x. split. 
assert (exists e', In e' (raisedevents x)). destruct (raisedevents x). unfold not in H6. exfalso. apply H6. auto.
exists r. simpl. left. auto. destruct H8. apply ConnectedTrans with (a2:=x) (e':=x0).
auto. apply ConnectedRefl. apply errorStuck. auto.  assert (exists e', In e' (raisedevents x) /\ ~(generalErrConfig e' x)).
apply inGenErr. auto. 
 
unfold not in H7. remember (raisedevents x). induction l. unfold not in H6. exfalso. apply H6. auto.
 destruct H8. destruct H8.    
           apply H with (a:=x) (n:=n0) (e:=x0) in H5.
destruct H5. destruct H5. remember H5. clear Heqc.   exists x1. split. apply ConnectedTrans with (a2:=x) (e':=x0). auto. auto.
auto.  apply termL5 with (conf:=a) (e:=e). auto. auto.
auto. 
generalize dependent x0. unfold not in n0.   
unfold stuckConfig in n0.   
unfold not. intros. rewrite Heql in H8. auto. auto. auto.   
Qed. 

(*used to bridge connected and chainMerge*)
Inductive ConnectedBack : configuration -> configuration -> raisedEvent -> Prop :=
| ConnectedBackRefl: forall a e, ConnectedBack a a e
| ConnectedBackTrans: forall a1 a2 a3 e1 e2, ConnectedBack a1 a2 e1 -> synchrony a2 a3 e2-> ConnectedBack a1 a3 e1.


Fixpoint Connected_RevApp {a1 a2 a3: configuration} {e e':raisedEvent} (pr: Connected a2 a3 e') (acc: ConnectedBack a1 a2 e) : ConnectedBack a1 a3 e.
  destruct pr.
  - assumption.
  - eapply Connected_RevApp.
    + eassumption.
    + eauto using ConnectedBackTrans.
Defined.

Lemma Connected_ConnectedBack :
  forall a1 a2 e, Connected a1 a2 e -> ConnectedBack a1 a2 e.
Proof.
  eauto using Connected_RevApp, ConnectedBackRefl.
Qed.

(*termination on ConnectedBack*)
Lemma TerminatesBack': forall a e, 
correct_configuration a
-> In e (raisedevents a)
-> ~(generalErrConfig e a)
-> exists a',  ConnectedBack a a' e /\  (stuckConfig a').
Proof.
intros. pose proof Connected_ConnectedBack.
pose proof TerminatesOnConnected'. 
destruct H3 with (a:=a) (e:=e). auto. auto. auto.
destruct H4.
apply H2 in H4. exists x. split. auto. auto.
Qed.       

Check constructConfigList. 

Check constructConfig.  

(*initial configuration has one pending event*)
Lemma initialConfigOneRaisedEvent: forall re conf re',
initialConfig conf -> In re (raisedevents conf) -> In re' (raisedevents conf) -> re = re'.
Proof. intros. unfold initialConfig in H.    
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
induction (raisedevents conf).  inversion H0. destruct l. destruct H0. destruct H1. rewrite <-  H0. auto.
inversion H1. inversion H0. inversion H2.
Qed.           

Lemma syncEvent: forall conf conf' re, synchrony conf conf' re -> In re (raisedevents conf). 
Proof.
intros. unfold synchrony in H. 
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
auto.
Qed.    


(*relation between ConnectedBack and chainMerge*)
 Lemma ConnectedBack_SmedlConnected :
  forall a1 a2 e, initialConfig a1 
-> In e (raisedevents a1)
->  ~(generalErrConfig e a1)
-> ConnectedBack a1 a2 e -> (a1 = a2 \/ chainMerge a1 a2 e).
Proof.
induction 4.
  - left. auto.  
  - remember H. clear Heqi.    apply IHConnectedBack in H. destruct H. Focus 2. right. eapply chain'. apply H. apply H3.
assert (In e2 (raisedevents a2)). apply syncEvent with a3. 
auto. assert (e1=e2). apply initialConfigOneRaisedEvent with a1. auto. auto. rewrite <- H in H4. auto.  rewrite <- H5 in H3. 
right. apply basic'. unfold initialConfig in i. 
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
apply H8 in H0. destruct H0.  auto. rewrite <-  H in H3. auto. auto. auto. 
Qed.



(*if an initial configuration cannot raise error, it is not stuck*)
Lemma InitialNotStuckNorError: forall a e, initialConfig a -> In e (raisedevents a) -> ~(generalErrConfig e a) ->  (~ stuckConfig a).
Proof.
intros. apply stepOrError with (e:=e) in H. destruct H.
unfold not in H1. exfalso. apply H1. auto. apply H in H1. unfold not. intros. unfold stuckConfig in H2.
apply H2 in H0. unfold not in H0. exfalso. apply H0. apply H1. auto.   
Qed. 


(*termination theorem*)
Theorem Terminates: forall conf e (p:stuckConfig conf + ~ stuckConfig conf), initialConfig conf
-> In e (raisedevents conf)
-> ~(generalErrConfig e conf)
->  (exists conf', chainMerge conf conf' e  /\ (stuckConfig conf')).
Proof.
intros. pose proof  TerminatesBack'. remember H. clear Heqi.  unfold initialConfig in H.  destruct H. destruct H3.
remember H0. clear Heqi0.   
apply H4 in H0. apply H2 with (e:=e) in H. Focus 2. auto. Focus 2. auto.
destruct H.           
exists x. split. Focus 2.  
destruct H. auto. 
destruct H.  
apply ConnectedBack_SmedlConnected in H. Focus 3. auto. Focus 3. auto. 
destruct H. rewrite <- H in H5.  Focus 2. unfold not in H1. auto. Focus 2. auto.    
assert (~ stuckConfig conf). apply InitialNotStuckNorError with e. auto. auto. auto. unfold not in H6. exfalso. apply H6. auto.  
Qed. 

(*end proof termination*)


(*Some aux definition and lemmas used for proving determinism*)


Lemma sceInFinished: forall lst conf conf'  conf'' sce,
 In sce (dom (controlstate conf)) ->
In sce (finishedscenarios conf'') ->
In conf'' lst ->
innerCombineFunc' conf None (lst) = Result conf' ->
In sce (finishedscenarios conf').
SearchAbout  finishedscenarios.
Proof.  intro lst. induction lst. 
- intros. inversion H1.
-  intros. destruct H1.
+ simpl in H2.  destruct lst. 
* simpl in H2. inversion H2;subst. rewrite <- H4. auto.
* simpl in H2. 
remember (innerCombineFunc' conf (Some c) lst).
destruct e. Focus 2. inversion H2. 
   SearchAbout finishedscenarios.  
pose proof finishedSceInvariant. eapply H3.
apply H. left. rewrite <- H1 in H0.  apply H0. symmetry. apply H2.
+ simpl in H2. destruct lst.
* inversion H1.
* simpl in H2. 
remember (innerCombineFunc' conf (Some c) lst).
destruct e. Focus 2. inversion H2.
  pose proof finishedSceInvariant. eapply H3.
apply H. assert (In sce (finishedscenarios v)). 
eapply IHlst. apply H. apply H0. apply H1. symmetry;auto. right. apply H4.
symmetry;auto.                         eauto.
Qed.       


Lemma reverseNoEnabledScenario: forall conf conf' sce e,
synchrony conf conf' e
-> In sce (dom (controlstate conf))
-> ~In sce (finishedscenarios conf')
-> ~ In sce (transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec) e conf) 
.
Proof. 
intros. unfold not; intros. unfold not in H1. apply H1.     
unfold synchrony in H.  
 repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
unfold combineFunc in H5. 
destruct (checkType conf e). 
remember (constructConfigList (dom (controlstate conf)) e conf).
destruct e0. destruct v. inversion H5. 
unfold constructConfigList in Heqe0. 
Focus 2. inversion H5. Focus 2. inversion H5.
SearchAbout constructConfigList'.          
assert (exists conf' : configuration, Result conf' = constructConfig sce e conf).
eapply termL2'. symmetry. apply Heqe0. auto.    
destruct H6.   
SearchAbout constructConfigList'.
assert (In x (c::v)).
eapply termL2''. symmetry. apply Heqe0. apply H2. auto. 
SearchAbout finishedscenarios.    
pose proof termL3. 
assert (finishedscenarios x = sce :: finishedscenarios conf).
apply H8 with (e:=e). auto.
eapply sceInFinished;eauto. rewrite H9;eauto. simpl;left;auto.
Qed.  
   

Lemma finishMergeInvariant: forall lst conf conf'  sce,
innerCombineFunc' conf None lst = Result conf'
-> In sce (dom (controlstate conf)) 
-> (exists conf1, In conf1 lst /\ In sce (finishedscenarios conf1))
-> In sce (finishedscenarios conf').
Proof. intro lst. induction lst.
- intros.   simpl in H. inversion H.
- intros. simpl in H . destruct lst. destruct H1. destruct H1. simpl in H. inversion H. rewrite H4 in H1.
simpl in H1. destruct H1. rewrite <- H1 in H2. auto. inversion H1. 
simpl in H. 
remember  (innerCombineFunc' conf (Some c) lst). 
destruct e. unfold mergeConfigFunc in H.    
destruct (mergeDataStateFunc (datastate conf) (datastate a) (datastate v)).        
destruct (mergeControlStateFunc (controlstate conf) (controlstate a) (controlstate v) ).
inversion H. simpl. destruct H1. destruct H1.  destruct H1. 
rewrite <- H1 in H2. Focus 2. 
clear H3.   assert (In sce (finishedscenarios v)). eapply IHlst. symmetry. simpl. apply Heqe. auto. destruct H1.
exists x. rewrite <- H1. split;simpl. left. auto. rewrite H1. auto. exists x. split. simpl;right. auto. auto. 
                   
unfold mergeList'. 

apply in_or_app. assert (In sce (finishedscenarios a) \/ ~ (In sce (finishedscenarios a))).
apply excluded_middle. destruct H4. left. auto. 
      right.      
SearchAbout filterList. apply filterIn. auto. auto. 
unfold mergeList'.   apply in_or_app;left;auto.
inversion H. inversion H. inversion H.
Qed.       


Lemma noEnabledScenario': forall conf conf' e sce,
synchrony conf conf' e
-> In sce (dom (controlstate conf))
-> ~In sce (finishedscenarios conf')
-> getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf').
Proof. intros. apply reverseNoEnabledScenario with (conf:=conf) (e:=e) in H1. 
 apply syncSceInvariant  with (conf':=conf') in H1;auto. auto. auto.   
Qed. 

(*1. prove if sce is not in the finishedScenario of conf', then its state
is not changed, meaning its value in controlstate is not changed *)
(*2. if state is not changed, then  
(transEvMap (Some state, Some (eventDefinition re))) is not changed, empty
but we need to prove that in the previous transition, its value is empty
 *)
Print getScenarioState. 

Lemma getScenarioNoError: forall conf  sce,
correct_configuration conf 
-> In sce (dom (controlstate conf))
-> (exists state, Some state = getScenarioState sce (controlstate conf)).
Proof. intros. destruct H.  apply sce_state_no_empty in H0.
unfold not in H0.  destruct (getScenarioState sce (controlstate conf)). exists s. auto.
  exfalso.   apply H0. auto.   
Qed. 

Lemma transCompl: forall l l1 re conf,
l1 = transformConfig l  re conf -> (forall sce, In sce l /\ ~ In sce l1 -> constructConfig sce re conf = Error error3).
Proof. intros. destruct H0. generalize dependent l2. 
induction l. 
- inversion H0.
- intros. destruct H0. rewrite  H0 in H.
Print transformConfig.   simpl in H.
destruct (constructConfig sce re conf). unfold not in H1. exfalso. apply H1. rewrite H. simpl. left. auto.      
    induction l2. simpl in H. destruct l. simpl in H.  
destruct (constructConfig a re conf). inversion H. destruct H0.  
remember (string_dec s error3). 
destruct s0. rewrite e. auto. inversion H3. 
destruct (string_dec s error3). rewrite e. auto. inversion H.  
destruct (string_dec s error3). rewrite e. auto. inversion H. 
destruct (string_dec s error3). rewrite e. auto. inversion H. 
rewrite H3 in H1. exfalso. apply H1. simpl. left. auto.
simpl in H. 
destruct (constructConfig a re conf ). Focus 2.        
destruct (string_dec s error3).  apply IHl with (l2:=l2). auto. auto. auto. destruct l2. 
inversion H. inversion H. unfold not in H1. simpl in H1. 
assert (~ In sce l2). unfold not. intros. apply H1. right. auto. apply IHl with l2;auto. 
destruct l2. inversion H. inversion H.  assert (~ In sce l2). unfold not. 
unfold not in H1. intros. apply H1. right. auto. apply IHl with l2;auto.
Qed.   


Lemma scenarioStateCase: forall conf conf' sce e,
synchrony conf conf' e -> In sce (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)->
(exists conf1, constructConfig sce e conf = Result conf1) \/ (constructConfig sce e conf = Error error3).
Proof. intros.    Print constructConfigList. 
assert ((exists conf1 : configuration, constructConfig sce e conf = Result conf1) 
\/ ~(exists conf1 : configuration, constructConfig sce e conf = Result conf1)). apply excluded_middle.
destruct H1. left. auto.
unfold not in H1. right. 
unfold synchrony in H.     
 repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
unfold combineFunc in H4. 
destruct (checkType conf e).  Focus 2. inversion H4.
remember (constructConfigList (dom (controlstate conf)) e conf).
destruct e0. Focus 2. inversion  H4.
destruct v. Focus 2. inversion H4. 
unfold constructConfigList in Heqe0. 
assert ((In sce (transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec) e conf))
\/ ~(In sce (transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec) e conf))).
apply excluded_middle. destruct H5. 
destruct (transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec) e conf).
inversion H5. simpl in Heqe0. destruct H5. 
remember (constructConfig s e conf). destruct e0. rewrite H5 in Heqe1. exfalso. apply H1. exists v0. symmetry. auto.
inversion Heqe0.  destruct (constructConfig s e conf). 
remember  (constructConfigList' l e conf). destruct e0. inversion Heqe0. subst. clear H6. clear Heqe0.        
pose proof termL2'. symmetry in Heqe1.  apply H6  with (sce:=sce) in Heqe1. 
destruct Heqe1. symmetry. exfalso. apply H1. exists x. symmetry. auto. auto. inversion Heqe0. inversion Heqe0. 
unfold not in H5.  SearchAbout transformConfig. pose proof transCompl.
apply H7 with (l:= (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))
 (l1:=  (transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec) e conf)) .
auto. split.  auto. auto. 
inversion H4.
Qed.     


Lemma transformFilter: forall l conf e sce x , 
constructConfig sce e conf = Result x -> 
In sce (l) 
-> In sce (transformConfig (l) e conf).
Proof. intro l. induction l.  
-  intros. inversion H0.    
- intros. simpl. destruct H0.
+ rewrite H0.   rewrite H. simpl;left;auto.
+  destruct (constructConfig a e conf). simpl;right. eapply IHl. apply H. auto.  
destruct (string_dec s error3).  eapply IHl. apply H. auto.  simpl. right. eapply IHl. apply H. auto. 
Qed.        



Lemma scenarioStateCase': forall conf conf' sce e,
correct_configuration conf -> synchrony conf conf' e 
-> In sce (filterList (finishedscenarios conf') (dom (controlstate conf)) scenario_dec)->
 (constructConfig sce e conf = Error error3).
Proof. intros. assert (~ exists conf', constructConfig sce e conf = Result conf').
unfold not. intros. destruct H2. assert (~ In sce  (finishedscenarios conf')).  eapply filterL1.
apply H1. unfold not in H3. apply H3. clear H3.  
pose proof termL23.   SearchAbout finishedscenarios.    
pose proof finishMergeInvariant. Focus 2.    
pose proof scenarioStateCase. apply H3 with (sce:=sce) in H0.
 destruct H0. exfalso;apply H2;auto. auto. SearchAbout finishedscenarios. 
SearchAbout filterList.  apply filterIn.  eapply filterL2. apply H1. 
assert (~(In sce  (finishedscenarios conf'))). 
eapply filterL1. apply H1. unfold not. intros. unfold not in H4. apply H4. SearchAbout finishedscenarios.   
pose proof finishedInvariantSync. 
eapply H6. apply H. apply H0. auto.     
 remember H0. clear Heqs.  unfold synchrony in H0. 
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. unfold combineFunc in H7.
destruct (checkType conf e). remember (constructConfigList (dom (controlstate conf)) e conf).
destruct e0. destruct v.   inversion H7.  
eapply H4. apply H7.   eapply filterL2. apply H1.  exists x. Focus 2. inversion H7.
Focus 2. inversion H7. split.
   Check termL2''. eapply termL2''.
symmetry. apply Heqe0. Focus 2. symmetry. apply H2. Focus 2. SearchAbout finishedscenarios.   
assert (finishedscenarios x = sce :: finishedscenarios conf). eapply termL3. symmetry. apply H2.
rewrite H8. simpl;left;auto. apply transformFilter with (x:=x). auto. 
              SearchAbout transformConfig. SearchAbout filterList. apply filterIn. 
eapply filterL2. apply H1. assert (~ In sce (finishedscenarios conf')). eapply filterL1. apply H1.
unfold not. intros. unfold not in H8. apply H8.       
Check finishedInvariantSync.  pose proof finishedInvariantSync. 
eapply H10. apply H. apply s. auto.     
Qed. 

(*Here we assume that each event in the alphabet corresponds to exactly one event instance*)
Axiom findNone: forall l conf e, findEventInstance e (datastate conf) (l) = None -> l = nil.

Lemma scenarioStateCase'': forall conf conf' sce e,
correct_configuration conf -> synchrony conf conf' e 
-> In sce (filterList (finishedscenarios conf') (dom (controlstate conf)) scenario_dec)->
 (constructConfig sce e conf' = Error error3).
Proof. intros. pose proof  scenarioStateCase'. 
pose proof noEnabledScenario'. 
 assert ( getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf')).
apply H3 with (e:=e). auto. eapply filterL2. apply H1. eapply filterL1. apply H1. 
 assert ( constructConfig sce e conf = Error error3). eapply H2. auto. apply H0. apply H1.
unfold constructConfig in H5. 
remember (getScenarioState sce (controlstate conf)).
destruct o.   remember  (findEventInstance e (datastate conf) (transEvMap (Some s, Some (eventDefinition e))) ).
destruct o.   Focus 2. unfold constructConfig. rewrite Heqo in H4. rewrite <- H4. rewrite <- Heqo. 
assert ((transEvMap (Some s, Some (eventDefinition e)))=nil). 
 symmetry in Heqo0. apply findNone in Heqo0. auto. rewrite H6. simpl. auto.
 
   
destruct (createValueEnv (eventArgs e0) (eventParams (eventDefinition e)) (eventArguments e) ).
destruct (valid (extendEnv v (datastate conf)) e0 sce conf).
destruct ( getStep conf sce e0). destruct (checkValueNonDeterminism conf e s0).
remember (configTransition (extendEnv v (datastate conf)) e e0 sce s0 conf).
destruct e1.  inversion H5. inversion H5.  inversion H5. inversion H5. inversion H5. inversion H5.
  inversion H5.     
Qed. 



Lemma transformConfigIsNull: forall l conf e,
(forall sce, In sce l -> constructConfig sce e conf = Error error3)
-> transformConfig l e conf = nil.
Proof.  intro l. induction l;intros.
- simpl. auto.  
-   simpl. assert (constructConfig a e conf = Error error3). apply H.
simpl;left;auto.  rewrite H0.  destruct (string_dec error3 error3).
apply IHl. intros. apply H. simpl;right;auto. exfalso;apply n;auto.
Qed.   

Lemma eventDefSame: forall conf conf' sce e,
correct_configuration conf -> synchrony conf conf' e 
-> In sce (filterList (finishedscenarios conf') (dom (controlstate conf)) scenario_dec)->
(forall ev, (eventDefinition ev = eventDefinition e) -> (constructConfig sce ev conf' = Error error3)).
Proof. intros. pose proof  scenarioStateCase'. 
pose proof noEnabledScenario'. 
 assert ( getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf')).
apply H4 with (e:=e). auto. eapply filterL2. apply H1. eapply filterL1. apply H1. 
 assert ( constructConfig sce e conf = Error error3). eapply H3. auto. apply H0. apply H1.
unfold constructConfig in H6. 
remember (getScenarioState sce (controlstate conf)).
destruct o.   remember  (findEventInstance e (datastate conf) (transEvMap (Some s, Some (eventDefinition e))) ).
destruct o.   Focus 2. unfold constructConfig. rewrite Heqo in H5. rewrite <- H5. rewrite <- Heqo. 
assert ((transEvMap (Some s, Some (eventDefinition e)))=nil). 
 symmetry in Heqo0. apply findNone in Heqo0. auto. rewrite H2.  rewrite H7. simpl. auto.
 
   
destruct (createValueEnv (eventArgs e0) (eventParams (eventDefinition e)) (eventArguments e) ).
destruct (valid (extendEnv v (datastate conf)) e0 sce conf).
destruct ( getStep conf sce e0). destruct (checkValueNonDeterminism conf e s0).
remember (configTransition (extendEnv v (datastate conf)) e e0 sce s0 conf).
destruct e1. inversion H6. assert (s1 = error3 \/ ~(s1=error3)).
apply excluded_middle. destruct H7. rewrite H7 in Heqe1.
inversion H6.  inversion H6. inversion H6. inversion H6. inversion H6.
  inversion H6.     inversion H6. 
Qed. 


Lemma transformEmpty: forall conf conf'  e,
correct_configuration conf -> synchrony conf conf' e 
-> (forall ev, (eventDefinition ev = eventDefinition e) ->
nil = transformConfig (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec) ev conf'). 
Proof. intros. pose proof  eventDefSame. 
assert (dom (controlstate conf) = dom (controlstate conf')).
apply domControlSync with (e:=e);auto. symmetry.
rewrite <- H3. 
eapply  transformConfigIsNull.
intros. eapply H2. apply H. apply H0. auto. auto.  
Qed.

Lemma uniqueRaisedEvent: forall conf conf' re, correct_configuration conf -> synchrony conf conf' re -> 
~(exists re' conf'', (eventDefinition re = eventDefinition re'/\ synchrony conf' conf'' re')).
Proof. 
intros. unfold not;intros.  destruct H1. destruct H1. destruct H1.
pose proof  transformEmpty.   
assert (nil = transformConfig (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec) x conf').
eapply H3. apply H. apply H0. symmetry. auto. 
unfold synchrony in H2.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
unfold combineFunc in H7. 
destruct (checkType conf' x).
unfold constructConfigList in H7. rewrite <- H4 in H7. simpl in H7. inversion H7. inversion H7.
Qed.        




(*begin main proof of determinism*)
(*The structure of the proof is finished*)
(*1. the equivalence relation of configuration is defined: equivConf*)
(*2. causal relation between events is defined :eventLeadTo*)
(*3. interference-free relation between events is defined: interference_free*)
(*4. sufficient condition for determinism is defined*)
(*5. diamond lemma is defined: not finished*)
(*6. one-step confluence lemma(weakConfluence) is defined: not finished*)
(*7. multi-step confluence lemma(confluence) is defined: not finished*)
(*8. determinism theorem is defined:not finished*)


(*collect all triggering event except imported events*)
Fixpoint TriggeringSet' (sce_env: scenario_env) : list event_definition
:= match sce_env with
| nil => nil
| (s,state)::env'=> mergeList' (filter (fun ev => if importEventBool ev then false else true)
 (stEvMap (Some state))) (TriggeringSet' env') (event_definition_dec)
end. 

(*collect all events*)
Definition TriggeringSet (conf:configuration) : list event_definition
:= TriggeringSet' (controlstate conf). 


Fixpoint getUpdatedByInstances (ei: event_instance) (sce_env:scenario_env): list atom :=
match sce_env with
| nil => nil
| (s,state)::env' => match stpStMap (state,ei) with
                             | None => getUpdatedByInstances ei env'
                             | Some stp => mergeList' (getUpdated (stepActions stp)) (getUpdatedByInstances ei env') (atom_eq_dec)
                             end
end. 

Fixpoint getUsedByInstances (ei: event_instance) (sce_env:scenario_env): list atom :=
match sce_env with
| nil => nil
| (s,state)::env' => match stpStMap (state,ei) with
                             | None => getUsedByInstances ei env'
                             | Some stp => mergeList' (getUsedFromActions (stepActions stp)) (getUsedByInstances ei env') (atom_eq_dec)
                             end
end. 

Fixpoint getUpdates (lst: list event_instance) (conf: configuration) : list atom :=
match lst with
| nil => nil
| ei::lst' => mergeList' (getUpdatedByInstances ei (controlstate conf)) (getUpdates lst' conf) (atom_eq_dec) 
end.


Fixpoint getUseds (lst: list event_instance) (conf: configuration) : list atom :=
match lst with
| nil => nil
| ei::lst' => mergeList' (getUsedByInstances ei (controlstate conf)) (getUseds lst' conf) (atom_eq_dec) 
end.
 


(*collect all used variables of an event*)
Definition UsedVarSet (conf:configuration) (e:event_definition) :list atom :=
filterListReverse (dom (datastate conf)) (getUseds (getEventInstances (e) (conf)) conf) (atom_eq_dec).

(*collect all updated variables of an event*)
Definition UpdatedVarSet (conf:configuration) (e:event_definition) :list atom :=
filterListReverse (dom (datastate conf)) (getUpdates (getEventInstances (e) (conf)) conf) (atom_eq_dec).

(*get all state machines whose alphabet contain event e*)
Fixpoint scenario_alphabet (sce_env:scenario_env)  (e:event_definition): list scenario :=
match sce_env with
| nil => nil
| (s,state)::env' => if inList (event_definition_dec) e (alphabet s) then s::scenario_alphabet env' e else scenario_alphabet env' e
end. 

(*two lists are disjointed*)
Definition listIntersectionEmptyProp (A:Type)   (lst1 : list A) (lst2: list A) : Prop :=
forall i1 i2, (In i1 lst1 -> ~ In i1 lst2) /\  (In i2 lst2 -> ~ In i2 lst1).


(*causal relation between events*)
Inductive eventLeadTo : configuration-> event_definition -> event_definition -> Prop :=
| leadBasicCase:  forall ev conf ev',  In ev' (getRaised (getEventInstances (ev) (conf)) (controlstate conf)) -> eventLeadTo conf ev ev'
| leadTransit: forall ev ev' ev'' conf, eventLeadTo conf ev ev' -> eventLeadTo conf ev' ev'' -> eventLeadTo conf ev ev''
. 
(*interference_free relation between two events*)
Inductive interference_free: configuration -> event_definition -> event_definition -> Prop :=
| dep : forall conf e1 e2, 
(listIntersectionEmptyProp (UpdatedVarSet conf e1)  (UpdatedVarSet conf e2) ) -> (listIntersectionEmptyProp (UpdatedVarSet conf e1) (UsedVarSet conf e2)) 
-> (listIntersectionEmptyProp  (UpdatedVarSet conf e2) (UsedVarSet conf e1) ) 
->  listIntersectionEmptyProp (scenario_alphabet (controlstate conf) e1)  (scenario_alphabet (controlstate conf) e2)
-> ~(exists e3, eventLeadTo conf e1 e3 /\ eventLeadTo conf e2 e3)
->  interference_free conf e1 e2
.

(*property to ensure determinism*)
Definition deter_property (conf:configuration) : Prop :=
(forall e1 e2, 
In e1 (TriggeringSet conf) /\ In e2 (TriggeringSet conf) 
/\ ~(eventLeadTo conf e1 e2) /\ ~(eventLeadTo conf e2 e1) -> (interference_free conf e1 e2))
.

(*no cycle*)
Definition noCyclicCausalRelation (conf:configuration) : Prop:=
forall e1, In e1 (TriggeringSet conf) ->
~(eventLeadTo conf e1 e1).


Inductive chainMergeWithEventList: configuration -> configuration  -> nat ->  Prop :=
| basic_case''' : forall conf conf' e, synchrony conf conf' e -> chainMergeWithEventList conf conf' (S O)
| inductive_case''': forall conf conf' conf'' n  e,  chainMergeWithEventList conf conf' n  -> synchrony conf' conf'' e ->  chainMergeWithEventList conf conf'' (S n)
.


(*equivlance relation between two configurations*)
Definition equivConf (conf conf':configuration) : Prop :=
(datastate conf) = (datastate conf') /\ (controlstate conf) = (controlstate conf')
/\ equivList (raisedevents conf) (raisedevents conf') /\ equivList (finishedscenarios conf) (finishedscenarios conf')
/\ equivList (exportedevents conf) (exportedevents conf').

(*equivConf is an equivalence relation*)
Lemma equivConf_Refl: forall x,
equivConf x x. 
Proof. intros. unfold equivConf;split;auto.
split;auto. split. apply Permutation_refl.   
split. 
 apply Permutation_refl.
 apply Permutation_refl.
Qed.

Lemma equivConf_Sym: forall x1 x2,
equivConf x1 x2 <-> equivConf x2 x1. 
Proof. intros. split.
- intros. unfold equivConf in H. 
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. 
unfold equivConf. split;auto. split; auto. split. unfold equivList in H1. unfold equivList.
apply Permutation_sym. auto.     unfold equivList in H2. unfold equivList.
split. 
apply Permutation_sym. auto.
apply Permutation_sym. auto.
- intros. unfold equivConf in H. 
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. 
unfold equivConf. split;auto. split; auto. split. unfold equivList in H1. unfold equivList.
apply Permutation_sym. auto.     unfold equivList in H2. unfold equivList.
split. 
apply Permutation_sym. auto. 
apply Permutation_sym. auto. 
Qed.     

Lemma equivConf_Trans: forall x1 x2 x3,
equivConf x1 x2 -> equivConf x2 x3 -> equivConf x1 x3. 
Proof. intros. unfold equivConf in H. unfold equivConf in H0.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. 
unfold equivConf. split;auto. rewrite H0 in H. auto.
split. rewrite H1 in H5. auto.
split. unfold equivList. unfold equivList in H6. unfold equivList in  H2.
eapply Permutation_trans. apply H6. auto.
split. 

unfold equivList. unfold equivList in H7. unfold equivList in  H7.
eapply Permutation_trans. apply H7. auto.
eapply Permutation_trans. apply H8. auto.
Qed. 

Lemma getStepEquiv: forall conf conf' sce e, 
equivConf conf conf' ->
getStep conf sce e = getStep conf' sce e.
Proof.
intros. unfold getStep. unfold equivConf in H. destruct H. destruct H0. 
rewrite H0. auto.
Qed.  

Lemma evalCondEquiv: forall env s conf conf', 
 evalCondition env s conf = evalCondition env s conf'.
Proof. intros.
unfold evalCondition.         
auto.
Qed.  

Lemma inEventDefEq: forall ev l, 
In ev l <-> In_event_definition ev l = true. 
Proof.
intros. induction l.
split.
- intros. inversion H.
- intros. simpl in H. inversion H.
- split. intros. simpl. 
destruct (event_definition_dec ev a ). auto. apply IHl. destruct H. exfalso;apply n;auto. auto.
intros. simpl in H. destruct (event_definition_dec ev a).
left;auto. apply IHl in H. right;auto.
Qed.             
            
Lemma inEventDefEqFalse: forall ev l, 
~In ev l <-> In_event_definition ev l = false. 
Proof.
intros. induction l.
split.
- intros. simpl. auto.  
- intros. unfold not. intros. inversion H0.  
- split. intros. unfold not in H. simpl. 
destruct (event_definition_dec ev a ). exfalso. apply H. left;auto. 
apply IHl. unfold not. intros. apply H. right;auto.
intros. unfold not. intros.  simpl in H. destruct (event_definition_dec ev a).
inversion H. destruct H0. exfalso;apply n;auto. apply IHl in H. exfalso;apply H;auto.     
Qed.   


(*this proof is easy, I can do it later*)
Lemma inDefEquiv: forall l1 ev  l2, 
equivList l1 l2 -> 
In_event_definition (ev) l1 = 
In_event_definition (ev) l2.
Proof. intro l2. induction l2. 
intros. destruct l2. simpl. auto. simpl.         
assert (~(Permutation nil (e::l2))).
apply Permutation_nil_cons. exfalso. apply H0;auto.
intros. destruct l0. 
assert ((Permutation  nil  (a::l2))).
apply Permutation_sym. auto.
assert (~(Permutation nil (a::l2))).
apply Permutation_nil_cons. exfalso. apply H1;auto.
simpl. 
assert (a=e \/ a<>e).
apply excluded_middle. destruct H0. 
rewrite H0.            
destruct (event_definition_dec ev e). auto. apply IHl2. rewrite H0 in H. 
eapply Permutation_cons_inv. apply H. 
destruct (event_definition_dec ev a). 
destruct (event_definition_dec ev e). 
auto. rewrite <- e0 in H. assert (In ev (e::l0)). eapply Permutation_in.
apply H. left;auto. destruct H1. exfalso;apply n;auto.          SearchAbout eventId. Print EventEquivalence.
symmetry. rewrite <- inEventDefEq. auto.
destruct (event_definition_dec ev e).
rewrite <- e0 in H. 
assert (In ev (a::l2)).  eapply Permutation_in.
apply Permutation_sym. apply H. left;auto.
destruct H1. rewrite e0 in H1. exfalso;apply H0;auto. 
 rewrite <- inEventDefEq. auto. 
remember (In_event_definition ev l2). 
remember (In_event_definition ev l0).
destruct b. 
 symmetry in Heqb.  rewrite <- inEventDefEq in Heqb. 
assert (In ev (e::l0)). 
eapply Permutation_in. apply H. right;auto. destruct H1. exfalso;apply n0;auto. 
 symmetry. rewrite inEventDefEq in H1. rewrite H1 in Heqb0 .   auto.
symmetry in Heqb.  rewrite <- inEventDefEqFalse in Heqb. unfold not in Heqb. 
assert (~In ev (e::l0)). unfold not.  intros. apply Heqb. destruct H1. exfalso;apply n0;auto. 
assert (In ev (a::l2)). eapply Permutation_in. apply Permutation_sym. apply H.
right;auto. destruct H2. exfalso;apply n;auto. auto.  unfold not in H1. 
destruct b0.  exfalso. apply H1.  symmetry in Heqb0.  apply <- inEventDefEq in Heqb0. right;auto.
auto.
Qed.     

Print In_scenario.  

(*easy to proof, come back later*)
Lemma inSceEquiv: forall sce l1 l2, 
equivList l1 l2 ->
(In_scenario sce l1) =
(In_scenario sce l2).
Proof. intros. induction H.
- auto.
-  simpl.  destruct (scenario_dec sce x). auto.
auto.
- simpl.  destruct (scenario_dec sce y). destruct (scenario_dec sce x). auto. auto.
destruct (scenario_dec sce x). auto. auto.
- rewrite IHPermutation1. auto.
Qed.     
      

Lemma validEquiv: forall env e sce conf conf',
equivConf conf conf' ->
valid env e sce conf = valid env e sce conf'. 
Proof. 
intros. unfold equivConf in H.    
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
unfold valid. 
assert (getStep conf sce e = getStep conf' sce e).
apply getStepEquiv. unfold equivConf;split;auto.

 rewrite H4. destruct (getStep conf' sce e).
Focus 2. auto. assert (evalCondition env s conf = evalCondition env s conf').
apply evalCondEquiv.   
assert (In_event_definition (event (stepEvent s)) (map (fun re : raisedEvent => eventDefinition re) (raisedevents conf))
= In_event_definition (event (stepEvent s)) (map (fun re : raisedEvent => eventDefinition re) (raisedevents conf'))).
 apply inDefEquiv. apply  mapPermu. auto. 
rewrite H5. rewrite H6.     
assert ((In_scenario sce (finishedscenarios conf)) = (In_scenario sce (finishedscenarios conf'))).
Check inSceEquiv. 
apply  inSceEquiv. auto. rewrite H7. auto.
Qed.    

Lemma rmEquiv: forall l re x y , 
equivList (removeEvent' re (y :: x :: l)) (removeEvent' re (x :: y :: l)).
Proof. intro l. induction l.
- intros. simpl.  destruct (raisedEvent_dec re y). destruct (raisedEvent_dec re x ). 
rewrite <- e. rewrite <- e0. constructor. constructor.
constructor. constructor.
destruct (raisedEvent_dec re x). constructor. constructor.
apply perm_swap.   
- intros. simpl. destruct (raisedEvent_dec re y).
destruct (raisedEvent_dec re x). rewrite <- e. rewrite <- e0. constructor. constructor. apply Permutation_refl.
constructor. constructor. apply Permutation_refl.
  destruct (raisedEvent_dec re x ). apply Permutation_refl.
   destruct (raisedEvent_dec re a ).
apply perm_swap. apply perm_swap.
Qed.   


Lemma removeEquiv: forall (l1 l2:list raisedEvent) (re:raisedEvent),
equivList    l1 l2 ->
equivList    (removeEvent' re l1) (removeEvent' re l2).
Proof. 
intros. induction H.
- intros. simpl. constructor.
- intros. simpl.      
destruct (raisedEvent_dec re x).
 auto.
apply perm_skip. auto.   
- intros.  induction l. 
+ apply rmEquiv.  
+ apply rmEquiv.          
- eapply perm_trans. apply IHPermutation1. apply IHPermutation2.
Qed.    



Lemma configTransEquiv: forall env e e0 sce s1 conf conf',
equivConf conf conf' -> 
(forall s, configTransition (env) e e0 sce s1 conf = Error s -> configTransition (env) e e0 sce s1 conf' = Error s)
/\ (forall conf1, configTransition (env) e e0 sce s1 conf = Result conf1 
-> (exists conf2, configTransition (env) e e0 sce s1 conf' = Result conf2 /\ equivConf conf1 conf2)).
Proof. intros. split.
- intros. unfold configTransition in H0.  unfold configTransition.
destruct (updateDataState env (stepActions s1)).
inversion H0. auto. 
- intros.   unfold configTransition. unfold configTransition in H0. 
destruct (updateDataState env (stepActions s1)). Focus 2. inversion H0.
unfold equivConf in H.  
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. 
SearchAbout removeEvent'. 
exists (
    {|
    datastate := v;
    controlstate := updateControlState (controlstate conf') sce s1;
    raisedevents := getRaisedEventsFromActions env e (stepActions s1) ++ removeEvent' e (raisedevents conf');
    exportedevents := filter (fun re : raisedEvent => EventKind_beq (eventKind (eventDefinition re)) Exported)
                        (getRaisedEventsFromActions env e (stepActions s1)) ++ exportedevents conf';
    finishedscenarios := sce :: finishedscenarios conf';
    srcstatefinishedscenarios := (sce, pre_state s1, eventDefinition e) :: srcstatefinishedscenarios conf';
    updatedvariableList := mergeList'
                             (updateUpdateVariables (updatedvariableList conf')
                                (getUpdatedVariablesFromScenario conf' s1) e)
                             (getNewUpdateVariables conf' e (getUpdatedVariablesFromScenario conf' s1))
                             updatedVariable_dec;
    usedvariableList := mergeList'
                          (updateUsedVariables (usedvariableList conf') (getUsedVariablesFromScenario conf' s1) e)
                          (getNewUsedVariables conf' e (getUsedVariablesFromScenario conf' s1)) usedVariable_dec |}).
split. 
+ auto. 
+ inversion H0. 
unfold equivConf. 
 simpl. split. auto.
   rewrite H1. split;auto. 
split.
apply Permutation_app_head.
apply removeEquiv. auto.
split. 
apply perm_skip. auto.
eapply Permutation_app_head. auto.
Qed.   
         


Lemma constructConfigEquiv: forall sce e conf conf',
equivConf conf conf' ->
(forall s, constructConfig sce e conf = Error s -> constructConfig sce e conf' = Error s)
/\ (forall conf1, constructConfig sce e conf = Result conf1 
-> (exists conf2,  constructConfig sce e conf' = Result conf2 /\ equivConf conf1 conf2)).
Proof. intros. split.
intros.  unfold constructConfig in H0.
unfold constructConfig. 
unfold equivConf in H.     
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. 
rewrite <- H1.
destruct (getScenarioState sce (controlstate conf)). 
rewrite <- H. Focus 2. auto.       
destruct (findEventInstance e (datastate conf) (transEvMap (Some s0, Some (eventDefinition e))) ).
Focus 2. auto.   
destruct (createValueEnv (eventArgs e0) (eventParams (eventDefinition e)) (eventArguments e)).
Focus 2. auto. 
Print valid.
Print getStep.   
assert ((valid (extendEnv v (datastate conf)) e0 sce conf) = (valid (extendEnv v (datastate conf)) e0 sce conf')).
apply validEquiv.
unfold equivConf;split;auto. rewrite <- H5.          
destruct (valid (extendEnv v (datastate conf)) e0 sce conf).
Focus 2. auto.  
assert (getStep conf sce e0 = getStep conf' sce e0). 
apply getStepEquiv. 
unfold equivConf;split;auto. rewrite <- H6.
destruct (getStep conf sce e0). 
assert ((checkValueNonDeterminism conf e s1) = (checkValueNonDeterminism conf' e s1)).
admit. rewrite <- H7. 
destruct (checkValueNonDeterminism conf e s1). Focus 2. auto. Focus 2. auto.
Print configTransition. 
pose proof configTransEquiv. 
destruct H8 with (env:= (extendEnv v (datastate conf))) (e:=e) (e0:=e0) (sce:=sce) (s1:=s1) (conf:=conf) (conf':=conf').
 unfold equivConf;split;auto. 
remember (configTransition (extendEnv v (datastate conf)) e e0 sce s1 conf).
 destruct e1. inversion H0.    
assert (configTransition (extendEnv v (datastate conf)) e e0 sce s1 conf' = Error s2).
apply H9. auto. rewrite H11. auto.     
intros.
unfold  constructConfig.
unfold constructConfig in H0. 
unfold equivConf in H.  
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
rewrite <- H1. 
destruct (getScenarioState sce (controlstate conf)).
Focus 2. inversion H0.
rewrite <- H. 
destruct (findEventInstance e (datastate conf) (transEvMap (Some s, Some (eventDefinition e)))).
Focus 2. inversion H0.
 destruct (createValueEnv (eventArgs e0) (eventParams (eventDefinition e)) (eventArguments e)).
Focus 2. inversion H0.
assert ( (valid (extendEnv v (datastate conf)) e0 sce conf) = (valid (extendEnv v (datastate conf)) e0 sce conf') ).        
apply validEquiv. unfold equiv;split;auto.
rewrite <- H5.     
destruct (valid (extendEnv v (datastate conf)) e0 sce conf).
Focus 2. inversion H0.
assert (getStep conf sce e0 = getStep conf' sce e0). 
apply getStepEquiv. unfold equivConf;split;auto.
rewrite <- H6.      
destruct (getStep conf sce e0).
Focus 2. inversion H0.
assert (checkValueNonDeterminism conf e s0 =  checkValueNonDeterminism conf' e s0).
admit.
rewrite <- H7.
destruct (checkValueNonDeterminism conf e s0).
Focus 2. inversion H0.
remember (configTransition (extendEnv v (datastate conf)) e e0 sce s0 conf).
destruct e1.
Focus 2. inversion H0.
pose proof configTransEquiv.
assert (equivConf conf conf'). unfold equivConf;split;auto.
apply H8  with (env:=(extendEnv v (datastate conf))) (e:=e) (e0:=e0) (sce:=sce) (s1:=s0) (conf:=conf) (conf':=conf') in H9.
destruct H9.
symmetry in Heqe1.    
apply H10 in Heqe1. 
destruct Heqe1.
destruct H11. 
rewrite H11. 
exists x. 
inversion H0. rewrite <- H14. split;auto.     
 
        
Admitted.

Lemma transformEquiv': forall l e conf conf',
equivConf conf conf' ->
equivList (transformConfig l e conf) (transformConfig l e conf').
Proof.
 intro. induction l.
- intros. simpl. apply Permutation_refl.
- intros. simpl. 
remember (constructConfig a e conf ).
remember (constructConfig a e conf' ).
destruct e0. destruct e1. unfold equivList. apply perm_skip. 
apply IHl. auto.      
destruct (string_dec s error3). Focus 2.   
unfold equivList. apply perm_skip. 
apply IHl. auto.  
Focus 2. destruct e1.   
destruct (string_dec s error3). Focus 2.  
unfold equivList. apply perm_skip. 
apply IHl. auto.      
Focus 2.   
destruct (string_dec s error3).
destruct (string_dec s0 error3).
unfold equivList. apply IHl. auto. 
Focus 2.         
destruct (string_dec s0 error3).
Focus 2.
unfold equivList. apply perm_skip. 
apply IHl. auto.  pose proof constructConfigEquiv.
remember H. clear Heqe2. apply H0 with (sce:=a) (e:=e) in e1.
destruct e1. symmetry in Heqe0. apply H1 in Heqe0. rewrite Heqe0 in Heqe1. 
inversion Heqe1. rewrite H4 in e0. exfalso;apply n;auto.
pose proof constructConfigEquiv.
remember H. clear Heqe2. apply H0 with (sce:=a) (e:=e) in e1.
destruct e1. symmetry in Heqe0. apply H1 in Heqe0. rewrite Heqe0 in Heqe1. 
inversion Heqe1. rewrite <- H4 in e0. exfalso;apply n;auto.
pose proof constructConfigEquiv.
remember H. clear Heqe2. apply H0 with (sce:=a) (e:=e) in e1.
destruct e1. symmetry in Heqe0. apply H1 in Heqe0. rewrite Heqe0 in Heqe1. inversion Heqe1.  
pose proof constructConfigEquiv.
remember H. clear Heqe2. apply H0 with (sce:=a) (e:=e) in e1.
destruct e1.  symmetry in Heqe0. apply H2 in Heqe0. destruct Heqe0.
destruct H3. rewrite <-  Heqe1 in H3.  inversion H3.  
Qed. 

Lemma transformEquiv: forall l1 l2 e conf conf',
equivConf conf conf' ->
equivList l1 l2 ->
equivList (transformConfig l1 e conf) (transformConfig l2 e conf').

Proof. intros. unfold equivList in H0. induction H0. 
- simpl. apply Permutation_refl.
- unfold equivList in IHPermutation. simpl. remember (constructConfig x e conf). 
remember (constructConfig x e conf'). destruct e0. 
destruct e1. 
apply perm_skip. auto.
pose proof constructConfigEquiv.
remember H. clear Heqe2. apply H1 with (sce:=x) (e:=e) in e0.
destruct e0. symmetry in Heqe0. apply H3 in Heqe0. destruct Heqe0.
destruct H4. rewrite H4 in Heqe1. inversion Heqe1.   
destruct e1. 
 pose proof constructConfigEquiv.
remember H. clear Heqe2. apply H1 with (sce:=x) (e:=e) in e0.
destruct e0. symmetry in Heqe0. apply H2 in Heqe0. rewrite Heqe0 in Heqe1. inversion Heqe1.
destruct (string_dec s error3).  
destruct (string_dec s0 error3). auto. 
 pose proof constructConfigEquiv.
remember H. clear Heqe2. apply H1 with (sce:=x) (e:=e) in e1.
destruct e1.  symmetry in Heqe0. apply H2 in Heqe0. rewrite Heqe0 in Heqe1. inversion Heqe1.
rewrite H5 in n. exfalso;apply n;auto.   destruct (string_dec s0 error3).
pose proof constructConfigEquiv.
remember H. clear Heqe2. apply H1 with (sce:=x) (e:=e) in e1.
destruct e1.  symmetry in Heqe0. apply H2 in Heqe0. rewrite Heqe0 in Heqe1. inversion Heqe1. 
rewrite H5 in e0. exfalso;apply n;auto. apply perm_skip. auto.        

- intros.  simpl.    remember (constructConfig y e conf).  destruct e0.      
remember (constructConfig x e conf ). destruct e0.    
remember ( constructConfig y e conf').
destruct e0.  
remember (constructConfig x e conf'). destruct e0.  unfold equivList. 
Focus 2. 
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=x) (e:=e) in e0.
destruct e0.  symmetry in Heqe1. apply H2 in Heqe1. destruct Heqe1.
destruct H3.  rewrite H3 in Heqe3. inversion Heqe3.   
(*Permutation_app*) 
assert (y::x::transformConfig l e conf = (app (app (y::nil) (x::nil)) (transformConfig l e conf))).
simpl. auto.
rewrite H0. 
assert (x::y::transformConfig l e conf' = (app (app (x::nil) (y::nil)) (transformConfig l e conf'))).
simpl. auto.
rewrite H1. apply Permutation_app. simpl.
apply perm_swap. apply transformEquiv'. auto. 
pose proof constructConfigEquiv.
remember H. clear Heqe3. apply H0 with (sce:=y) (e:=e) in e0.
destruct e0.  symmetry in Heqe0. apply H2 in Heqe0. destruct Heqe0.
destruct H3.  rewrite H3 in Heqe2. inversion Heqe2.   
 destruct (string_dec s error3).   
remember (constructConfig x e conf'). 
remember (constructConfig y e conf').
destruct e1.    
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=x) (e:=e) in e1.
destruct e1.  symmetry in Heqe1. apply H1 in Heqe1.  rewrite Heqe1 in Heqe2. inversion Heqe2.
destruct (string_dec s0 error3).
destruct e2. apply perm_skip. apply transformEquiv'. auto. 
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=y) (e:=e) in e2.
destruct e2.  symmetry in Heqe0. apply H2 in Heqe0. destruct Heqe0.
destruct H3.  rewrite H3 in Heqe3. inversion Heqe3.      
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=x) (e:=e) in e1.
destruct e1.  symmetry in Heqe1. apply H1 in Heqe1. 
rewrite Heqe1 in Heqe2. inversion Heqe2. rewrite H4 in n. exfalso;apply n;auto.    
  remember (constructConfig x e conf' ).
destruct e0. 
pose proof constructConfigEquiv.
remember H. clear Heqe3. apply H0 with (sce:=x) (e:=e) in e0.
destruct e0.  symmetry in Heqe1. apply H1 in Heqe1. 
rewrite Heqe1 in Heqe2. inversion Heqe2. 
remember (constructConfig y e conf').
destruct e0.   
destruct (string_dec s0 error3). 
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=x) (e:=e) in e1.
destruct e1.  symmetry in Heqe1.  apply H1 in Heqe1. 
rewrite Heqe1 in Heqe2. inversion Heqe2.  
rewrite <- H4 in n. exfalso;apply n;auto.     
assert (y::x::transformConfig l e conf = (app (app (y::nil) (x::nil)) (transformConfig l e conf))).
simpl. auto.
rewrite H0. 
assert (x::y::transformConfig l e conf' = (app (app (x::nil) (y::nil)) (transformConfig l e conf'))).
simpl. auto.
rewrite H1. apply Permutation_app. simpl.
apply perm_swap. apply transformEquiv'. auto.
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=y) (e:=e) in e0.
destruct e0.  symmetry in Heqe0. apply H2 in Heqe0. destruct Heqe0.
destruct H3.  rewrite H3 in Heqe3. inversion Heqe3.    
destruct (string_dec s error3).  
remember (constructConfig x e conf ).
destruct e1.
remember (constructConfig x e conf').
destruct e1.
remember (constructConfig y e conf' ).
destruct e1. 
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=y) (e:=e) in e1.
destruct e1.  symmetry in Heqe0. apply H1 in Heqe0.
 rewrite Heqe0 in Heqe3. inversion Heqe3.
destruct (string_dec s0 error3).
apply perm_skip. apply transformEquiv'. auto.
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=y) (e:=e) in e1.
destruct e1.  symmetry in Heqe0. apply H1 in Heqe0. 
rewrite Heqe0 in Heqe3. inversion Heqe3. rewrite  H4 in n. exfalso;apply n;auto.
pose proof constructConfigEquiv.
remember H. clear Heqe3. apply H0 with (sce:=x) (e:=e) in e1.
destruct e1.  symmetry in Heqe1.  apply H2 in Heqe1. destruct Heqe1. destruct H3.   
rewrite H3 in Heqe2. inversion Heqe2.   
remember (constructConfig y e conf'). 
destruct e1.
pose proof constructConfigEquiv.
remember H. clear Heqe3. apply H0 with (sce:=y) (e:=e) in e1.
destruct e1.  symmetry in Heqe0. apply H1 in Heqe0. 
rewrite Heqe0 in Heqe2. inversion Heqe2.  
remember (constructConfig x e conf').
destruct e1.
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=x) (e:=e) in e1.
destruct e1.  symmetry in Heqe1.  apply H1 in Heqe1. 
rewrite Heqe1 in Heqe3. inversion Heqe3.
destruct (string_dec s0 error3).
destruct (string_dec s2 error3).       
destruct (string_dec s1 error3). apply transformEquiv'. auto.
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=y) (e:=e) in e3.
destruct e3.  symmetry in Heqe0. apply H1 in Heqe0. 
rewrite Heqe0 in Heqe2. inversion Heqe2. rewrite H4 in n. exfalso;apply n;auto.
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=x) (e:=e) in e2.
destruct e2.  symmetry in Heqe1.  apply H1 in Heqe1. 
rewrite Heqe1 in Heqe3. inversion Heqe3. rewrite H4 in n. exfalso;apply n;auto.
destruct (string_dec s2 error3).
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=x) (e:=e) in e2.
destruct e2.  symmetry in Heqe1.  apply H1 in Heqe1. 
rewrite Heqe1 in Heqe3. inversion Heqe3. rewrite H4 in e1. exfalso;apply n;auto.
destruct (string_dec s1 error3). apply perm_skip. apply transformEquiv'. auto.
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=y) (e:=e) in e1.
destruct e1.  symmetry in Heqe0. apply H1 in Heqe0. 
rewrite Heqe0 in Heqe2. inversion Heqe2. rewrite H4 in n1. exfalso;apply n1;auto.
remember (constructConfig x e conf).
remember (constructConfig x e conf' ).
destruct e0. destruct e1.    
remember (constructConfig y e conf' ).
destruct e0. 
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=y) (e:=e) in e0.
destruct e0.  symmetry in Heqe0. apply H1 in Heqe0. 
rewrite Heqe0 in Heqe3. inversion Heqe3.  
destruct (string_dec s0 error3). 
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=y) (e:=e) in e1.
destruct e1.  symmetry in Heqe0. apply H1 in Heqe0. 
rewrite Heqe0 in Heqe3. inversion Heqe3. rewrite H4 in e0. exfalso;apply n;auto.
assert (y::x::transformConfig l e conf = (app (app (y::nil) (x::nil)) (transformConfig l e conf))).
simpl. auto.
rewrite H0. 
assert (x::y::transformConfig l e conf' = (app (app (x::nil) (y::nil)) (transformConfig l e conf'))).
simpl. auto.
rewrite H1. apply Permutation_app. simpl.
apply perm_swap. apply transformEquiv'. auto.
pose proof constructConfigEquiv.
 remember H. clear Heqe3. apply H0 with (sce:=x) (e:=e) in e0.
destruct e0.  symmetry in Heqe1.  apply H2 in Heqe1. destruct Heqe1. destruct H3.   
rewrite H3 in Heqe2. inversion Heqe2.
destruct e1.
pose proof constructConfigEquiv.
 remember H. clear Heqe3. apply H0 with (sce:=x) (e:=e) in e0.
destruct e0.  symmetry in Heqe1.  apply H1 in Heqe1. 
rewrite Heqe1 in Heqe2. inversion Heqe2.
remember (constructConfig y e conf').
destruct e0. 
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=y) (e:=e) in e0.
destruct e0.  symmetry in Heqe0. apply H1 in Heqe0. 
rewrite Heqe0 in Heqe3. inversion Heqe3. 
destruct (string_dec s2 error3). 
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=y) (e:=e) in e1.
destruct e1.  symmetry in Heqe0. apply H1 in Heqe0. 
rewrite Heqe0 in Heqe3. inversion Heqe3. rewrite H4 in e0. exfalso;apply n;auto.
destruct ( string_dec s0 error3).
destruct  (string_dec s1 error3).
apply perm_skip.  apply transformEquiv';auto.
pose proof constructConfigEquiv.
 remember H. clear Heqe4. apply H0 with (sce:=x) (e:=e) in e1.
destruct e1.  symmetry in Heqe1.  apply H1 in Heqe1. rewrite Heqe1 in Heqe2.
inversion Heqe2. rewrite H4 in n1.  exfalso;apply n1;auto.
 destruct (string_dec s1 error3). 
pose proof constructConfigEquiv.
remember H. clear Heqe4. apply H0 with (sce:=x) (e:=e) in e1.
destruct e1.  symmetry in Heqe1.  apply H1 in Heqe1. rewrite Heqe1 in Heqe2.
inversion Heqe2. rewrite H4 in e0.  exfalso;apply n1;auto.
assert (y::x::transformConfig l e conf = (app (app (y::nil) (x::nil)) (transformConfig l e conf))).
simpl. auto.
rewrite H0. 
assert (x::y::transformConfig l e conf' = (app (app (x::nil) (y::nil)) (transformConfig l e conf'))).
simpl. auto.
rewrite H1. apply Permutation_app. simpl.
apply perm_swap. apply transformEquiv'. auto. 

-  unfold equivList in IHPermutation1. unfold equivList in IHPermutation2. 
unfold equivList.   eapply  perm_trans. apply IHPermutation1.
assert (Permutation ((transformConfig l'0 e conf')) ((transformConfig l'0 e conf))).
apply transformEquiv'. SearchAbout equivConf.  rewrite equivConf_Sym. auto.   
 eapply  perm_trans. apply H0. auto.
Qed.    


Print constructConfig. 
Lemma constructConfigListError: forall scs conf x e,
constructConfigList' scs e conf = Error x ->
(exists sce x, In sce scs /\ constructConfig sce e conf = Error x).
Proof.  intro scs.
induction scs.
- intros. simpl in H. inversion H.
- intros. simpl in H. 
  remember (constructConfig a e conf). 
destruct e0.    
remember (constructConfigList' scs e conf ).
destruct e0. inversion H.
symmetry in Heqe1.  
apply IHscs in Heqe1. destruct Heqe1. destruct H0. destruct H0. 
exists x0. exists x1. split. right;auto. auto.
exists a. exists s. split. left;auto. symmetry;auto.
Qed.                 






Lemma constructConfigListEquiv': forall scs e conf conf' x,
equivConf conf conf' ->
constructConfigList' scs e conf = Error x ->
(exists x', constructConfigList' scs e conf' = Error x').
Proof. intro scs. induction scs.
- intros. simpl in H0. inversion H0.
- intros. simpl in H0. 
remember (constructConfig a e conf).
destruct e0.  remember (constructConfigList' scs e conf).
destruct e0. inversion H0.
simpl.  
remember (constructConfig a e conf' ).
pose proof constructConfigEquiv. 
remember H. clear Heqe3.
eapply H1 in e1. 
destruct e1. 
remember (Heqe0). clear Heqe3.   symmetry in e1. 
apply H3 in e1. destruct e1. destruct H4. rewrite H4 in Heqe2. rewrite Heqe2. 
remember H. clear Heqe3. eapply IHscs in e1. Focus 2. symmetry. apply Heqe1.    destruct e1.
rewrite H6. exists x1. auto. simpl. 
pose proof constructConfigEquiv. 
remember H. clear Heqe1. eapply H1  in e0.
destruct e0. symmetry in Heqe0. apply H2 in Heqe0. rewrite Heqe0. exists s. auto.    
Qed.                      


Lemma constructConfigListEquiv: forall scs scs' e conf conf' x,
equivConf conf conf' ->
equivList scs scs' ->
 constructConfigList' scs e conf = Error x ->
(exists x', constructConfigList' scs' e conf' = Error x').  
Proof. intros. 
generalize dependent conf. generalize dependent e. generalize dependent conf'. generalize dependent x.  
induction H0.
- intros. simpl in H1. inversion H1.
- intros. simpl in H1.  simpl. remember (constructConfig x e conf ). 
destruct e0.  Focus 2. pose proof constructConfigEquiv.
inversion H1. remember H. clear Heqe1. eapply H2 in e0. destruct e0.
symmetry in Heqe0. remember Heqe0. clear Heqe1. apply H3 in e0. 
rewrite e0. exists s. auto. 
remember (constructConfig x e conf' ). destruct e0. Focus 2.
 exists s;auto.
remember (constructConfigList' l e conf).  destruct e0. Focus 2. 
assert ( exists x' : string, constructConfigList' l'0 e conf' = Error x').
eapply IHPermutation. apply H.   symmetry.  apply Heqe2.
destruct H2.   
exists x1. rewrite H2. auto. 
inversion H1. 
- intros. simpl in H1. 
simpl.        
remember (constructConfig y e conf).
destruct e0. remember (constructConfig x e conf ).
destruct e0. 
remember (constructConfigList' l e conf).
destruct e0. inversion H1.           
pose proof constructConfigEquiv.
remember H. clear Heqe3.
eapply H0 in e0. 
destruct e0. 
remember Heqe0. clear Heqe3. 
symmetry in Heqe0.  apply H3 in Heqe0. destruct Heqe0. destruct H4.
remember Heqe1. clear Heqe0.  pose proof constructConfigEquiv.  remember H. clear Heqe0. 
eapply H6 in e2. destruct e2. symmetry in e1. 
apply H8 in e1. destruct e1. destruct H9. rewrite H9. rewrite H4. 
pose proof constructConfigListEquiv'. 
remember H. clear Heqe0. eapply H11 in e1. Focus 2. symmetry in Heqe2. apply Heqe2. 
destruct e1. rewrite H12. exists x3. auto.
pose proof constructConfigEquiv. 
remember H. clear Heqe2. eapply H0 in e0.
destruct e0. symmetry in Heqe1.  eapply H2 in Heqe1. 
rewrite Heqe1. exists s. auto.
destruct (constructConfig x e conf'). Focus 2. exists s0. auto. 
pose proof constructConfigEquiv.     
remember H. clear Heqe1. eapply H0 in e0.
destruct e0. symmetry in Heqe0.   eapply H2 in Heqe0. 
rewrite Heqe0. exists s. auto.
- intros. remember H. clear Heqe0. 
eapply IHPermutation1 in e0. Focus 2. apply H1. 
remember H. clear Heqe1. 
destruct e0. pose proof constructConfigListEquiv'.
assert (equivConf conf' conf). apply equivConf_Sym. auto.   
 eapply H2 in H3.  Focus 2. apply H0. destruct H3.     
 eapply IHPermutation2.  apply H. apply H3.
Qed.    
 
(*relation between two configuration lists*)
(*similar to permutation, but use equivConf instead of equal*)
Inductive confEquivList: list configuration -> list configuration -> Prop :=
| confEqBasic: confEquivList nil nil 
| confEqSkip: forall conf conf' l l', equivConf conf conf' -> confEquivList l l'
                -> confEquivList (conf::l) (conf'::l')
| confEqSwap: forall conf1 conf1' conf2 conf2' l l', equivConf conf1 conf1' -> equivConf conf2 conf2' -> confEquivList l l'
                     -> confEquivList (conf1::conf2::l) (conf2'::conf1'::l')
| confEqTrans: forall l1 l2 l3, confEquivList l1 l2 -> confEquivList l2 l3 -> confEquivList l1 l3.

Lemma confEquivList_length_eq: forall  l l',
 confEquivList l l' -> 
length l = length l'.
Proof.
intros. induction H.
- auto.
- Print confEquivList. simpl. f_equal. auto.
- intros. simpl. f_equal. f_equal. auto.
- rewrite  IHconfEquivList1. auto.
Qed.      

Lemma confEquivList_sym: forall l l',
confEquivList l l' ->
confEquivList l' l.
Proof. intros. 
induction H. 
- constructor. 
- Print confEquivList.  apply confEqSkip. apply equivConf_Sym. auto. auto.
-   Print confEquivList. apply  confEqSwap. apply equivConf_Sym. auto.
apply equivConf_Sym. auto. auto.
-Print confEquivList. eapply confEqTrans. apply IHconfEquivList2. auto.
Qed.       

Lemma confEquivList_refl: forall  l,
confEquivList l l.
Proof. intros. 
induction l;constructor. 
- apply equivConf_Refl.  
- auto.  
Qed.  

Lemma confEquivList_cons_nil: forall  x l,
~ confEquivList nil (x::l) .
Proof.
intros. unfold not. intros. assert (@length configuration nil = length (x::l)).
apply confEquivList_length_eq. auto. inversion H0. 
Qed.       

Lemma confEquivListTransitivity: forall conf1 x x0,
confEquivList conf1 x ->
confEquivList x x0 ->
confEquivList conf1 x0. 
Proof.
intros. Print confEquivList.
eapply confEqTrans.
apply H. apply H0.   
Qed.  


Lemma sceEqualConfig: forall e conf a sce v1 v2, 
Result v1 = constructConfig sce e conf ->
Result v2 = constructConfig a e conf ->
v1 = v2 ->
sce = a.
Proof.  intros. SearchAbout finishedscenarios.   
pose proof termL3.
apply H2 in H. 
apply H2 in H0.
rewrite H1 in H. 
rewrite H in H0. inversion H0. auto.   
Qed. 

Lemma constructNotIn: forall l e conf sce v1 v2,
Result v1 = constructConfig sce e conf ->
Result v2 = constructConfigList' l e conf ->
~ In sce l ->
~ In v1 v2.
Proof.  intro l. induction l.
- intros. simpl in H0. inversion H0. unfold not. intros. inversion H2.
- intros. simpl in H0.  
remember (constructConfig a e conf ).
destruct e0. Focus 2. inversion H0. 
remember (constructConfigList' l e conf).
destruct e0. Focus 2. inversion H0.
inversion H0. unfold not; intros. destruct H2. 
rewrite <- H2 in H. 
unfold not in H1. apply H1. left.  
eapply sceEqualConfig.  apply Heqe0. 
apply H. auto. unfold not in IHl.  eapply IHl. 
apply H. apply Heqe1. intros. unfold not in H1. apply H1. right;auto. auto.       
Qed. 

Lemma constructListUniq: forall l e conf  v1,
Result v1 = constructConfigList' l e conf ->
uniqList l ->
uniqList v1.
Proof. intro l. induction l.
- intros. simpl in H. inversion H. constructor.
- intros. inversion H0;subst. simpl in H. 
 remember (constructConfig a e conf ).
destruct e0. Focus 2. inversion H. 
remember (constructConfigList' l e conf ).
destruct e0. Focus 2. inversion H.
inversion H. 
constructor. 
eapply IHl. apply Heqe1. apply H3. 
pose proof constructNotIn.
eapply H1. apply Heqe0. apply Heqe1. auto.
Qed.      


Lemma constructListScsEquiv: forall l e conf conf' v1,
Result v1 = constructConfigList' l e conf ->
equivConf conf conf' ->
uniqList l ->
(exists v2, Result v2 = constructConfigList' l e conf' /\ confEquivList v1 v2).
Proof.  intro l. induction l.
- intros. simpl in H. inversion H. exists nil.
simpl. split;auto.  constructor. 
- intros. simpl in H.              
remember (constructConfig a e conf ).
destruct e0. Focus 2. inversion H. 
 remember (constructConfigList' l e conf).
destruct e0.
Focus 2. inversion H. 
pose proof  constructConfigEquiv.
remember H0. clear Heqe2. apply H2 with (sce:=a) (e:=e) in e0.
destruct e0. remember Heqe0. clear Heqe2. symmetry in e0. apply H4 in e0.
destruct e0. destruct H5. 
remember Heqe1. clear Heqe2. apply IHl with (conf':=conf') in e0. 
destruct e0. destruct H7. exists (x::x0).
split. simpl. rewrite H5. rewrite <- H7. auto.
inversion H. Focus 2. auto. constructor. auto. auto. inversion H1;auto.     
Qed.              

SearchAbout constructConfig.                                           

             
          
Lemma   PermuUniq: forall  (A:Type) l1 l2,
Permutation l1 l2 ->
@uniqList A l1 -> 
@uniqList A l2.
Proof. intros. induction H.
- constructor.
- constructor. apply IHPermutation. inversion H0;auto. inversion H0. subst. unfold not.  intros. unfold not in H4. 
apply H4.  eapply Permutation_in.  assert (Permutation l'0 l). apply Permutation_sym.
auto. apply H2. auto. 
- constructor. constructor. inversion H0;subst. inversion H2;auto. inversion H0;subst. unfold not. intros.
unfold not in H3. apply H3. right;auto. 
unfold not. intros.
inversion H0;subst.  unfold not in H4. apply H4. destruct H. left;auto.
inversion H3;subst. exfalso;apply H6;auto.
- apply IHPermutation2. apply IHPermutation1. auto.    
Qed. 



Lemma constructListEquiv: forall scs scs' conf conf' conf1 e,
equivConf conf conf' ->
equivList scs scs' ->
Result conf1 = constructConfigList' scs  e conf->
uniqList scs ->
uniqList scs' ->
(exists conf2, Result conf2 = constructConfigList' scs'  e conf' /\
confEquivList conf1 conf2).
Proof. intros. generalize dependent conf. 
generalize dependent conf'.
 generalize dependent conf1.
 generalize dependent e.

 induction H0.
- intros. simpl in H1. inversion H1. simpl.
exists nil. split. auto.  constructor. 
- intros.   simpl.  simpl in H1.    remember (constructConfig x e conf ).
destruct e0. Focus 2. inversion H1. 
remember (constructConfigList' l e conf).
destruct e0. Focus 2. inversion H1.
pose proof constructConfigEquiv.
remember H. clear Heqe2. apply H4 with (sce:=x) (e:=e) in e0.
destruct e0. remember Heqe0. clear Heqe2.  symmetry in Heqe0. apply H6 in Heqe0.
destruct Heqe0. destruct H7.
rewrite H7. 
remember (constructConfigList' l'0 e conf'). 
destruct e1. Focus 2. pose proof constructConfigListEquiv. 
remember H. clear Heqe2. assert (equivConf conf' conf). SearchAbout equivConf. 
apply equivConf_Sym. auto.   apply H9 with (scs:=l'0) (scs':=l) (x:=s) (e:=e) in H10.
destruct H10.   rewrite <- Heqe1 in H10. inversion H10. apply Permutation_sym. auto. symmetry. auto.
remember H. clear Heqe2.
apply IHPermutation with (e:=e) (conf1:=v0) in e1. 
destruct e1. destruct H9.    exists (x0::v1). intros. split. auto.     
inversion H1. rewrite <- Heqe0 in H9. inversion H9;subst. Focus 2.    
auto. inversion H2. auto.  constructor. auto. auto. inversion H3;auto. auto.  
- intros. 
simpl in H1.  
remember (constructConfig y e conf).
destruct e0. Focus 2. inversion H1.
remember ( constructConfig x e conf ).
destruct e0. Focus 2. inversion H1.
remember (constructConfigList' l e conf).
destruct e0. Focus 2. inversion H1.    
simpl.
pose proof constructConfigEquiv.
remember H. clear Heqe3.
apply H0  with (sce:=x) (e:=e) in e0.

destruct e0.
remember Heqe1. clear Heqe3. 
symmetry in e0. 
apply H5 in e0.
destruct e0.
destruct H6.
rewrite H6.
remember H. clear Heqe3. 
apply H0 with (sce:=y) (e:=e) in e0.
destruct e0. 
remember Heqe0.
clear Heqe3.
symmetry in e0. apply H9 in e0. 
destruct e0. 
destruct H10.
rewrite H10.
remember (constructConfigList' l e conf'). 
pose proof constructListScsEquiv.
remember Heqe2. clear Heqe4.
apply H12 with (conf':=conf') in e1. Focus 2.
auto. destruct e1. destruct H13.
rewrite <- H13 in Heqe3. rewrite Heqe3. 
exists (x0::x1::x2).
split;auto.
inversion H1. Print confEquivList.
eapply confEqSwap. auto. auto. auto.
inversion H2;auto. inversion H15;auto.                    
- intros.  
remember H. clear Heqe0. apply IHPermutation1 with (e:=e) (conf1:=conf1) in e0.
destruct e0. destruct H0. 
remember H. clear Heqe0.
 assert (equivConf conf' conf).
apply equivConf_Sym. auto.  
apply IHPermutation2 with (e:=e) (conf1:=x) in H5.
Focus 2. SearchAbout uniqList.  eapply PermuUniq. apply H0_.   auto. Focus 2. auto. 
destruct H5. destruct H5.
          
pose proof constructListScsEquiv. remember H5. clear Heqe1.
apply H7 with (conf':=conf') in e1.
Focus 2. auto.
destruct e1. destruct H8. exists x1. split.
auto. 
         
assert (confEquivList conf1 x0).
eapply confEquivListTransitivity.
apply H4. auto.
eapply confEquivListTransitivity.
apply H10. auto. auto. auto. auto.   
eapply PermuUniq. apply H0_. auto. auto.    
Qed.        

Lemma mergeListEquiv: forall (A:Type) l1 l1' l2 l2' decA, 
equivList l1 l2 ->
equivList l1' l2' ->
equivList (@mergeList' A l1 l1' decA) (@mergeList' A l2 l2' decA).
Proof. intros.
unfold mergeList'.
 SearchAbout filterList. 
apply Permutation_app. auto.  
apply filterListEquiv'. auto. auto.
Qed.   

Lemma filterNil: forall (A:Type) l1' decA,
(@filterList A Datatypes.nil l1' decA = l1').
Proof. intros. induction l1'. auto. simpl. rewrite IHl1'. auto.
Qed. 


Lemma filterNoEffect: forall (A:Type) l0 l1 l2  decA, 
uniqList (app l1 l2) ->
uniqList l0 ->
(forall i, In i l1 -> ~ In i l0) ->
@filterList A (app l1 l2) l0 decA= @filterList A l2 l0 decA.
Proof. intros A l0. 
induction l0.
- intros. simpl. auto.
- intros. simpl.       
remember (inList decA a (l2 ++ l3)).
destruct b. 
remember (inList decA a l3).
destruct b. 
apply IHl0. auto. inversion H0;subst;auto. intros. unfold not. intros.
apply H1 in H2. unfold not in H2. apply H2. right;auto. 
assert (In a l2). assert (In a (l2++l3)). SearchAbout inList.  eapply reverseinListLemma. 
symmetry. apply Heqb. assert (~In a l3). eapply reverseinListFalse. symmetry.  apply Heqb0.
assert (In a l2 \/ In a l3). apply in_app_or. auto. destruct H4. auto. exfalso;apply H3;auto.   
apply H1 in H2. unfold not in H2. exfalso. apply H2. left;auto.
remember (inList decA a l3 ).
destruct b. 
assert (~In a (l2++l3)). eapply reverseinListFalse. symmetry.  apply Heqb. 
assert (In a l3).    eapply reverseinListLemma. 
symmetry. apply Heqb0. unfold not in H2. exfalso;apply H2. 
apply in_or_app. right;auto.     
f_equal. apply IHl0. auto. inversion H0;subst;auto. 
intros. unfold not. intros.
apply H1 in H2. unfold not in H2. apply H2. right;auto.
Qed. 
                         

Lemma appendFilterEquiv: forall (A:Type) a l1 l2 decA,
In a l2 -> 
~In a l1 ->
uniqList l1 ->
uniqList l2 ->
Permutation (a::@filterList A (a::l1) l2 decA) (filterList (l1) l2 decA).
Proof. intros.  generalize dependent a. generalize dependent l2. induction l0.
- intros. inversion H.
- intros. destruct H.
+ rewrite H. simpl.             
destruct (decA a0 a0). Focus 2. exfalso;apply n;auto.
remember (inList decA a0 l2).
destruct b. SearchAbout inList. assert (In a0 l2).
eapply reverseinListLemma. symmetry in Heqb. apply Heqb.
exfalso;apply H0;auto.  apply perm_skip.  
inversion H2;subst.
assert (filterList (a0 :: l2) l0 decA =  filterList l2 l0 decA).  
pose proof filterNoEffect.
assert (a0::l2 = app (a0::nil) l2).       simpl.
auto. rewrite H3. 
apply H. simpl. Print uniqList. apply uniqL_push. auto. auto. auto.
intros. destruct H4. rewrite <- H4.
auto. inversion H4. rewrite H. apply Permutation_refl. 
+ simpl. inversion H2;subst.   
destruct (decA a a0). rewrite e in H6. exfalso;apply H6;auto.
remember (inList decA a l2).
destruct b.
apply IHl0. auto. auto. auto. auto.      
assert (Permutation (a0 :: a :: filterList (a0 :: l2) l0 decA) (a :: a0 :: filterList (a0 :: l2) l0 decA)).
apply perm_swap.
assert  (Permutation (a :: a0 :: filterList (a0 :: l2) l0 decA) (a :: filterList l2 l0 decA)).
apply perm_skip. apply IHl0. auto. auto. auto. auto.
eapply perm_trans. 
apply H3. apply H4.          
 Qed. 

Lemma middleMergeListEquiv: forall (A:Type) l2 l0 a decA,
uniqList l2 ->
uniqList l0 ->
In a l0 ->
~In a l2 ->
equivList (a::(app l2  (@filterList A (a::l2) l0 decA))) (app l2 (@filterList A l2 l0 decA)).
Proof. intros A l2. 
induction l2. 
- intros. simpl. destruct l0. inversion H1. simpl.
destruct H1.       
destruct (decA a0 a). rewrite e. 
inversion H0;subst.    
rewrite filterNil. 
assert (filterList (a :: Datatypes.nil) l0 decA = filterList nil l0 decA).
assert (app (a::nil) nil = a::nil).
simpl. auto. rewrite <- H1. 
apply filterNoEffect. simpl. 
Print uniqList. 
apply uniqL_push. Print uniqList. apply uniqL_nilL.
unfold not;intros. inversion H3. auto. intros. assert (i = a).
destruct H3. auto. inversion H3. rewrite H4. auto. 
rewrite H1. rewrite filterNil. apply Permutation_refl. exfalso;apply n;auto.
destruct (decA a0 a).
inversion H0;subst.
exfalso;apply H6;auto.
inversion H0;subst.  
rewrite filterNil.     
assert (Permutation  (a :: a0 :: filterList (a :: Datatypes.nil) l0 decA)  (a0 :: a :: filterList (a :: Datatypes.nil) l0 decA) ).
apply perm_swap.
assert  (Permutation (a0 :: a :: filterList (a :: Datatypes.nil) l0 decA) (a0::l0)).
assert (Permutation  (a :: filterList (a :: Datatypes.nil) l0 decA) l0).
rewrite <- filterNil with (decA:=decA).  
apply appendFilterEquiv. auto. auto. constructor. auto.     
 apply perm_skip. auto.  eapply perm_trans. apply H3. auto.
-   intros. simpl. inversion H;subst.
assert (Permutation (a0 :: a :: (l2 ++ filterList (a0 :: a :: l2) l0 decA)%list) (a::a0::(l2 ++ filterList (a0 :: a :: l2) l0 decA)%list)).
apply perm_swap. assert (Permutation ((a :: a0 :: (l2 ++ filterList (a0 :: a :: l2) l0 decA)%list)) ( (a :: (l2 ++ filterList (a :: l2) l0 decA)%list))).
apply perm_skip. 

assert (Permutation (app l2 (a0::(filterList(a0::a::l2) l0 decA))) (app l2 (filterList (a :: l2) l0 decA))).

apply Permutation_app_head.   
apply appendFilterEquiv. auto. auto. auto. auto. 
assert (Permutation (a0 :: (l2 ++ filterList (a0 :: a :: l2) l0 decA)%list) ( (l2 ++ a0 :: filterList (a0 :: a :: l2) l0 decA))).
apply Permutation_middle. 
eapply perm_trans. apply H7. apply H4. 
eapply perm_trans. apply H3. auto.         
Qed. 


Lemma mergeListSymEquiv: forall (A:Type) l1 l2 decA,
uniqList l1 ->
uniqList l2 ->
equivList  (@mergeList' A l1 l2 decA) (@mergeList' A l2 l1 decA) .
Proof.
intros A l1.  induction l1.
intros. unfold mergeList'.
simpl.
 rewrite app_nil_r. 
rewrite filterNil. apply Permutation_refl.
intros. unfold mergeList'. 
unfold mergeList' in IHl1.
simpl.    
remember (inList decA a l0).
destruct b. 
SearchAbout inList.             
assert (In a l0).
eapply reverseinListLemma. symmetry in Heqb. apply Heqb.
inversion H;subst.  
Print filterList.
assert (Permutation   (l2 ++ filterList l2 l0 decA) (l0 ++ filterList l0 l2 decA)).
apply IHl1. auto. auto. 
assert (Permutation (a :: (l2 ++ filterList (a :: l2) l0 decA)%list) (l2 ++ filterList l2 l0 decA)).        
 apply middleMergeListEquiv. auto. auto. auto. auto. eapply perm_trans.
apply H3. apply H2.
assert (Permutation (l0 ++ a :: filterList l0 l2 decA) (a::(app l0 (filterList l0 l2 decA)))).
apply Permutation_sym. apply Permutation_middle.   
assert (Permutation (a :: (l2 ++ filterList (a :: l2) l0 decA)%list) (a :: (l0 ++ filterList l0 l2 decA)%list)).
apply perm_skip.
assert (a::l2=(app (a::nil) l2)).
simpl. auto. rewrite H2. 
rewrite filterNoEffect. Focus 2. simpl. auto. Focus 2. auto. Focus 2. intros.
destruct H3. rewrite <- H3. auto. 
SearchAbout inList.  eapply reverseinListFalse. symmetry. apply Heqb. inversion H3. 
apply IHl1. inversion H;auto. auto. 
eapply perm_trans. apply H2. apply Permutation_sym. auto.                              
Qed. 



Lemma mergeListPermu': forall  (A:Type) l0 l l'' decA,
uniqList l0 ->
uniqList l ->
uniqList l'' ->
Permutation l l'' ->
Permutation (@mergeList' A l0 l decA) (@mergeList' A l0 l'' decA).
Proof.
intros. unfold mergeList'. 
apply Permutation_app_head. 
generalize dependent l0. 
induction H2.
- intros. simpl. constructor.
- intros. simpl. 
 remember (inList decA x l0). destruct b.
apply IHPermutation. inversion H0;auto. inversion H1;auto. auto. 
apply perm_skip. apply IHPermutation. inversion H0;auto. inversion H1;auto. auto. 
- intros. simpl.    
remember (inList decA y l0). destruct b.
  remember (inList decA x l0).
destruct b.
apply Permutation_refl.
apply Permutation_refl.
remember (inList decA x l0).
destruct b.
apply Permutation_refl.
constructor.
- intros. 
apply perm_trans with (filterList l0 l'0 decA). 
apply IHPermutation1. auto.        
eapply PermuUniq. apply H2_. auto. auto. 
apply IHPermutation2.      
eapply PermuUniq. apply H2_. auto. auto. 
auto. 
Qed. 

Lemma filterListSkip: forall (A:Type) l0 l y x decA ,
uniqList (y::x::l) ->
~In x l0 ->
@filterList A (y :: x :: l) l0 decA = @filterList A (y :: l)  l0 decA.
Proof. intros A l0.
induction l0.   
- intros. simpl. auto.
- intros.  simpl.  
destruct (decA a y). 
apply IHl0.  auto. unfold not; intros. unfold not in H0. apply H0. right;auto.
destruct (decA a x).
remember (inList decA a l). destruct b.
rewrite e in Heqb.
inversion H;subst. inversion  H3;subst. 
assert (In x l). eapply reverseinListLemma. symmetry. apply Heqb.
exfalso;apply H6;auto. 
rewrite e in H0. destruct H0. left;auto. 
remember (inList decA a l).
destruct b. 
apply IHl0. auto.  unfold not. intros. unfold not in H0. apply H0. right;auto.
f_equal. apply IHl0. auto.   unfold not. intros. unfold not in H0. apply H0. right;auto.
Qed.            


Lemma mergeListEquivE': forall (A:Type) l l1 l1'  decA, 
uniqList l1 ->
uniqList l1' ->
equivList l1 l1' ->
uniqList l ->
equivList (@mergeList' A l l1' decA) (@mergeList' A l1 l decA).
Proof. 
intros. generalize dependent l. 
induction H1.
- intros.  unfold mergeList'. simpl.  
rewrite app_nil_r. 
rewrite filterNil. 
 apply Permutation_refl.
- intros. unfold mergeList'. simpl.
remember (inList decA x l0).
destruct b.     
inversion H;subst.
inversion H0;subst.  
assert (Permutation (x :: (app l (filterList (x :: l) l0 decA))) (app l  (x ::filterList (x :: l) l0 decA))).

apply Permutation_middle. 
assert (Permutation (x :: (app l (filterList (x :: l) l0 decA))) (l ++ filterList l l0 decA)).
assert  (Permutation (l0 ++ filterList l0 l'0 decA) (l ++ filterList l l0 decA)).
unfold mergeList' in IHPermutation.  
apply IHPermutation.  auto. auto. auto. 
apply middleMergeListEquiv. auto. auto. auto.     auto. SearchAbout inList. eapply reverseinListLemma. symmetry in Heqb. apply Heqb.
auto.
apply Permutation_sym.   
eapply perm_trans. apply H4.  
apply Permutation_sym.
apply  IHPermutation. auto. auto. auto. 
assert (Permutation ((x :: (app l  (filterList (x :: l) l0 decA)%list))) ((app l (x :: (filterList (x :: l) l0 decA)%list)))).
apply Permutation_middle. 
assert (x::l = app (x::nil) l).
simpl. auto. 
assert (filterList ((x :: Datatypes.nil) ++ l) l0 decA = filterList l l0 decA). 
apply filterNoEffect. simpl. auto. auto. intros. destruct H5. rewrite <- H5. SearchAbout inList.
eapply reverseinListFalse. symmetry in Heqb. apply Heqb. inversion H5. 
rewrite <- H4 in H5. rewrite H5 in H3. rewrite H5. 
assert (Permutation (app l0  (x :: filterList l0 l'0 decA)) (x:: (app l0  ( filterList l0 l'0 decA)))).
apply Permutation_sym. apply Permutation_middle. 
assert (Permutation (x :: (l0 ++ filterList l0 l'0 decA)%list) (x :: (l ++ filterList l l0 decA)%list)).
apply perm_skip. unfold mergeList' in IHPermutation.  apply IHPermutation. inversion H;auto. inversion H0;auto. auto. 
eapply perm_trans. apply H6. apply H7.
- intros. unfold mergeList'. 
simpl. 
remember (inList decA x l0). destruct b. 
remember (inList decA y l0). destruct b.
assert (y::x::(app l (filterList (y :: x :: l) l0 decA)) =  y::(app (x::l) (filterList (y :: x :: l) l0 decA))).
simpl. auto. rewrite H1.
assert (Permutation (y :: ((x :: l) ++ filterList (y :: x :: l) l0 decA)%list) ((x::l)++filterList (x :: l) l0 decA)%list). 
apply middleMergeListEquiv.
inversion H;subst. auto. auto. SearchAbout inList. eapply  reverseinListLemma. symmetry. apply Heqb0.
inversion H;auto. 
assert ((((x :: l) ++ filterList (x :: l) l0 decA) %list) = (x::((app l  ( filterList (x :: l) l0 decA)%list)))).       
simpl. auto. 
assert (Permutation  (x :: (l ++ filterList (x :: l) l0 decA)%list) (l++filterList (l) l0 decA)%list).
 apply middleMergeListEquiv.
inversion H;subst. inversion H7;subst. auto. auto.  eapply  reverseinListLemma. symmetry. apply Heqb.
 inversion H;auto. subst. inversion H7;auto.
rewrite <- H4 in H5.  
apply Permutation_sym.
eapply perm_trans. apply H3. 
eapply perm_trans. apply H5.
 apply mergeListSymEquiv. inversion H. inversion H8;auto. auto.
assert (Permutation (l0 ++ y :: filterList l0 l decA) (y :: (app l0 (filterList l0 l decA)))).
apply  Permutation_sym. apply Permutation_middle. 
assert (y::x::l = app (y::nil)  (x::l)).
simpl.  auto. 
rewrite H3. 
rewrite filterNoEffect. Focus 2. simpl. auto. Focus 2. auto. Focus 2. intros. destruct H4;auto. rewrite <- H4.
SearchAbout inList. eapply  reverseinListFalse. symmetry. apply Heqb0. 
assert (Permutation  (x :: (app l  (filterList (x :: l) l0 decA))) (app l (filterList l l0 decA))).
apply middleMergeListEquiv. inversion H. inversion H6;auto. auto. 
SearchAbout inList.  eapply  reverseinListLemma. symmetry. apply Heqb. inversion H.
inversion H6. auto.   
eapply perm_trans. apply H1. 
apply perm_skip. 
apply Permutation_sym. 
eapply perm_trans. apply H4. 
apply  mergeListSymEquiv.  inversion H. inversion H7;auto. auto.
remember (inList decA y l0).
destruct b. 
assert (Permutation (l0 ++ x :: filterList l0 l decA) (x :: (app l0 (filterList l0 l decA)))).
apply  Permutation_sym. apply Permutation_middle. 
assert (Permutation (y :: x :: (l ++ filterList (y :: x :: l) l0 decA)%list) (x :: y :: (l ++ filterList (y :: x :: l) l0 decA)%list)).
constructor. 
eapply perm_trans. apply H1. 
apply Permutation_sym. eapply perm_trans.
apply H3. 
constructor. 
assert  (filterList (y :: x :: l) l0 decA = filterList (y::l) l0 decA).
apply filterListSkip. auto.    eapply reverseinListFalse. symmetry. apply Heqb.  
rewrite H4. 
assert (Permutation (y :: (l ++ filterList (y :: l) l0 decA)%list) ((l ++ filterList ( l) l0 decA)%list)).
apply  middleMergeListEquiv. inversion H. inversion H7;auto. auto.
 eapply  reverseinListLemma. symmetry in Heqb0. apply Heqb0. inversion H0. inversion H7. auto.
eapply perm_trans. apply H5. 
apply mergeListSymEquiv. inversion H. inversion H8;auto. auto.
assert (y::x::l = app (y::x::nil) l). simpl. auto.
rewrite H1. 
rewrite filterNoEffect. Focus 2. simpl. auto. Focus 2. auto. Focus 2. intros. destruct H3.  rewrite <- H3.
SearchAbout inList. 
eapply reverseinListFalse. symmetry.  apply Heqb0. destruct H3. rewrite <- H3.
 eapply reverseinListFalse. symmetry.  apply Heqb.     inversion H3.
assert (Permutation (app l0  (x :: y :: filterList l0 l decA)) (x::(app l0 (y::(filterList l0 l decA))))).
apply Permutation_sym. apply Permutation_middle.
assert (Permutation (app l0 (y :: filterList l0 l decA)%list) (y :: (app l0  (filterList l0 l decA)%list))).
apply Permutation_sym. apply Permutation_middle.
assert  (Permutation (x :: (l0 ++ y :: filterList l0 l decA)%list) (x :: (y :: (l0 ++ filterList l0 l decA)%list))).
constructor. apply H4. 
eapply perm_trans. apply H3. 
eapply perm_trans. apply H5. 
assert (Permutation (y :: x :: (l ++ filterList l l0 decA)%list)  (x :: y :: (l ++ filterList l l0 decA)%list)).
constructor. 
apply Permutation_sym. eapply perm_trans. apply H6. 
apply perm_skip. apply perm_skip.
 apply mergeListSymEquiv. inversion H. inversion H9. auto. auto.                                                                                

- intros.  assert (equivList (mergeList' l0 l'0 decA) (mergeList' l l0 decA)).
apply IHPermutation1. auto.  eapply PermuUniq. apply H1_ . auto. auto.    
assert (equivList (mergeList' l l'' decA) (mergeList' l'0 l decA)).
apply IHPermutation2.  eapply PermuUniq. apply H1_ . auto.  
eapply PermuUniq. apply H1_0. eapply PermuUniq. apply H1_. 
auto. auto. 
apply Permutation_sym.  apply  Permutation_sym in H1. 
eapply perm_trans. apply H1.
 apply Permutation_sym in H1. 
eapply perm_trans. apply H1.      
rewrite mergeListSymEquiv at 1. 
Focus 2. auto. Focus 2. auto. 
assert (Permutation  (mergeList' l0 l'' decA)  (mergeList' l'' l0 decA)).
apply  mergeListSymEquiv. auto. 
eapply PermuUniq. apply H1_0. eapply PermuUniq. apply H1_. 
auto. auto.  
eapply mergeListPermu'. auto. auto. auto. apply perm_trans with l'0. auto. auto.    
Qed.   


Lemma mergeConfigEquiv: forall conf conf' conf1 conf2 conf1' conf2' conf3,
equivConf conf conf' ->
equivConf conf1 conf2 ->
equivConf conf1' conf2' ->
Result conf3 = mergeConfigFunc conf conf1 conf1'
-> (exists conf3', Result conf3' = mergeConfigFunc conf' conf2 conf2' /\ equivConf conf3 conf3').
Proof. 
intros. unfold equivConf in H.
unfold equivConf in H0.
unfold equivConf in H1.       
unfold mergeConfigFunc.
unfold mergeConfigFunc in H2.  
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
rewrite <- H.
rewrite <- H0.
rewrite <- H1.
rewrite <- H11.
rewrite <- H7. 
rewrite <- H3.
 remember (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf1')).
destruct e. Focus 2. inversion H2.
remember (mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf1') ).
destruct e.
Focus 2. inversion H2.
 exists ({|
    datastate := v;
    controlstate := v0;
    raisedevents := mergeList' (raisedevents conf2) (raisedevents conf2') raisedEvent_dec;
    exportedevents := mergeList' (exportedevents conf2) (exportedevents conf2') raisedEvent_dec;
    finishedscenarios := mergeList' (finishedscenarios conf2) (finishedscenarios conf2') scenario_dec;
    srcstatefinishedscenarios := mergeList' (srcstatefinishedscenarios conf2) (srcstatefinishedscenarios conf2')
                                   scenarioState_dec;
    updatedvariableList := mergeList' (updatedvariableList conf2) (updatedvariableList conf2') updatedVariable_dec;
    usedvariableList := mergeList' (usedvariableList conf2) (usedvariableList conf2') usedVariable_dec |}).
inversion H2. split.
auto.
unfold equivConf;split;simpl. auto.
split. auto.           
 Print mergeList'. 
split. apply mergeListEquiv.
auto. auto.
split. apply mergeListEquiv.
auto. auto.
apply mergeListEquiv.
auto. auto.
Qed.     

Lemma noDataConf: forall dso a t r r0 r1  ds1 ds2,
noDataConflict ((a, (t, r)) :: dso) ((a, (t, r0)) :: ds1) ((a, (t, r1)) :: ds2)
-> (r<>r0 /\ r<>r1 -> r0 = r1) . 
Proof. 
intros. unfold noDataConflict in H. destruct H with a.
destruct H1.         
assert (getValue a ((a, (t, r0)) :: ds1) = getValue a ((a, (t, r1)) :: ds2)).
apply H2. split. destruct H0.
unfold not. intros.
simpl in H4. destruct a;inversion H1.         
remember (atom_eq_dec (AIdent s) (AIdent s)).
destruct s0. inversion H4. exfalso;apply H0;auto.
exfalso;apply n;auto. 
unfold not. intros. 
simpl in H3.
destruct a;inversion H1. 
destruct ((atom_eq_dec (AIdent s) (AIdent s))).
destruct H0. inversion H3. exfalso;apply H4;auto. exfalso;apply n;auto. 
simpl in H3. 
destruct a;inversion H1.   
destruct ((atom_eq_dec (AIdent s) (AIdent s))).
inversion H3;auto.  exfalso;apply n;auto. 
Qed.

Lemma  getValueNotIn: forall ds a, ~ In a (dom ds) -> getValue a ds = None.
Proof. intros. 
unfold not in H. induction ds.
simpl. destruct a;auto.
simpl. destruct a;auto. 
destruct a0. destruct p.  
remember (atom_eq_dec (AIdent s) a).
destruct s0. 
exfalso. apply H. rewrite e. simpl. left;auto.
apply IHds. intros. apply H. simpl. right;auto.
Qed.         


Print correct_configuration. 
Lemma noDataConf': forall dso a t r r0 r1  ds1 ds2,
uniqList (dom ((a, (t, r)) :: dso)) ->
uniqList (dom ((a, (t, r0)) :: ds1)) ->
uniqList (dom ((a, (t, r1)) :: ds2)) ->
noDataConflict ((a, (t, r)) :: dso) ((a, (t, r0)) :: ds1) ((a, (t, r1)) :: ds2)
-> noDataConflict (dso) (ds1) (ds2) . 
Proof.
 intros.          unfold noDataConflict in H2.
unfold noDataConflict.
intros. destruct H2 with s.  
split. auto.
intros. destruct H5. 

    assert (a=s \/ a<>s).
apply excluded_middle.
destruct H7.
rewrite H7 in H4. 
assert (r=r0 \/ r<>r0).
apply excluded_middle. destruct H8. 
inversion H0. 
inversion H1.
assert (getValue s ds1 = None).
rewrite <- H7. apply getValueNotIn. auto.    
assert (getValue s ds2 = None).
rewrite <- H7. apply getValueNotIn. auto. rewrite H17. rewrite H18. auto.      
 assert (getValue s dso = None).
inversion H. subst. apply getValueNotIn. auto.     
assert (getValue s ds1 = None).
inversion H0;subst. apply getValueNotIn. auto.     
rewrite H9 in H5. rewrite H10 in H5. 
exfalso;apply H5;auto.
assert (getValue s ((a, (t, r0)) :: ds1) = getValue s ((a, (t, r1)) :: ds2)).
apply H4. split. 
unfold not.  unfold not in H5. intros. apply H5. 
 simpl in H8.
destruct H3. destruct s; inversion H3.  
destruct (atom_eq_dec (AIdent s) a). exfalso;apply H7. auto.
auto.
unfold not.  unfold not in H6. intros. apply H6. 
 simpl in H8.
destruct H3. destruct s; inversion H3.  
destruct (atom_eq_dec (AIdent s) a). exfalso;apply H7. auto.
auto.
  simpl in H8.
destruct H3. destruct s; inversion H3.    
destruct (atom_eq_dec (AIdent s) a). exfalso;apply H7. auto. 
auto.     
Qed.  


Lemma mergeDataStateFuncSym: forall dso ds1 ds2, 
uniqList (dom (dso)) ->
uniqList (dom ( ds1)) ->
uniqList (dom (ds2)) ->
noDataConflict dso ds1 ds2 -> 
mergeDataStateFunc dso ds1 ds2 = mergeDataStateFunc dso ds2 ds1. 
Proof. intro dso.
induction dso.
intros. simpl. auto.
intros. simpl.
destruct ds1.
destruct ds2. simpl. auto. auto. simpl. destruct p.  simpl.
destruct p. simpl. auto. 
destruct ds2. simpl. destruct p. destruct p. auto.
destruct a. destruct p.  
remember (atom_eq_dec a a0).
destruct s. rewrite e. Focus 2.    
destruct p0. 
destruct (atom_eq_dec a a1). destruct p0. auto.
destruct p0. auto.
destruct p0. 
remember (atom_eq_dec a0 a1).
destruct s. Focus 2.
destruct p0. auto.
destruct p1. destruct p. destruct p0.
remember (typ_eq_dec t t0).
destruct s.
Focus 2. destruct (typ_eq_dec t t1);auto.
remember (typ_eq_dec t t1).
destruct s. Focus 2. auto.

assert (mergeDataStateFunc dso ds1 ds2   = mergeDataStateFunc dso ds2 ds1).

rewrite e in H2. rewrite e0 in H2. rewrite <- e1 in H2. rewrite <- e2 in H2. 
apply IHdso.
inversion H;auto. inversion H0;auto. inversion H1;auto.  
eapply noDataConf'. apply H. rewrite <- e in H0.   apply H0.
rewrite e. rewrite e0. apply H1. clear Heqs0. 
rewrite <- e in e0. rewrite e0. apply H2.   
rewrite H3. 
remember (mergeDataStateFunc dso ds2 ds1).
destruct e3. Focus 2. auto.

remember (range_typ_dec r0 r1).
destruct s. 
remember (range_typ_dec r1 r0).
destruct s. rewrite e3. auto. exfalso;apply n;auto.      
remember (range_typ_dec r0 r).
destruct s. 
remember (range_typ_dec r1 r0).
destruct s. auto.            
remember (range_typ_dec r1 r).
destruct s. rewrite  e3. rewrite <- e4. auto.
auto.     
remember (range_typ_dec r1 r0).
destruct s. rewrite e3. auto.
remember (range_typ_dec r1 r).
destruct s. auto.          

Print mergeDataStateFunc.   
rewrite  e in H2.
rewrite e0 in H2. rewrite <- e1 in H2. rewrite <- e2 in H2.
assert (r=r1).
unfold noDataConflict in H2.
destruct H2 with (s:=a1).
destruct H4.  
assert (getValue a1 ((a1, (t, r0)) :: ds1) = getValue a1 ((a1, (t, r1)) :: ds2)).
apply H5. split.  
Print getValue.          
 simpl.
destruct a1. inversion H4. inversion H4. inversion H4.
remember (atom_eq_dec (AIdent s) (AIdent s)).
destruct s0.          
unfold not. intros.
inversion H6. exfalso;apply n0;auto. exfalso;apply n3;auto. inversion H4. inversion H4.
inversion H4. 
simpl. 
destruct a1;inversion H4. 
remember (atom_eq_dec (AIdent s) (AIdent s)).
destruct s0. 
unfold not. intros.
inversion H6. exfalso;apply n0;auto. exfalso;apply n2;auto.  exfalso;apply n3;auto.
inversion H6.  
destruct a1;inversion H4. 
destruct (atom_eq_dec (AIdent s) (AIdent s)).
inversion H8. exfalso;apply n1;auto.  exfalso;apply n3;auto.
exfalso;apply n2;auto.      
Qed.  

Lemma getScenarioNotIn: forall cs  a, ~In a (dom cs) -> getScenarioState a cs = None.
Proof. intro cs.
induction cs.
- intros. simpl. auto.
- intros. simpl. 
destruct a.
remember (string_dec (scenarioId a0) (scenarioId s)).
destruct s1.  unfold not in H. exfalso. apply H. left. 
SearchAbout scenarioId.
pose proof  ScenarioEquivalence.  destruct H0 with (sce1:=a0) (sce2:=s).
destruct H1. auto. simpl;auto.   
apply IHcs. unfold not. intros.
unfold not in H. apply H. right;auto.
Qed.      

Lemma noControlConf': forall cso cs1 cs2 s s0 s2 s4,
uniqList (dom ((s, s0) :: cso)) -> 
uniqList (dom ((s, s2) :: cs1)) -> 
uniqList (dom ((s, s4) :: cs2)) ->
noControlConflict ((s, s0) :: cso) ((s, s2) :: cs1) ((s, s4) :: cs2)
-> noControlConflict cso cs1 cs2.
Proof.
intros. unfold  noControlConflict in H2.
unfold noControlConflict. 
intros. 
assert (s1=s \/ s1<>s).
apply excluded_middle.
destruct H5.
+   inversion H;subst. inversion H0;subst. inversion H1;subst.
assert (getScenarioState s cs1 = None). apply getScenarioNotIn. auto. 
assert (getScenarioState s cs2 = None). apply getScenarioNotIn. auto.
rewrite H5. rewrite H6. auto.
+          
Print  getScenarioState.  
  (* getValueNotIn: forall ds a, ~ In a (dom ds) -> getValue a ds = None.*)
assert (getScenarioState s1 ((s, s2) :: cs1) = getScenarioState s1 ((s, s4) :: cs2)).
apply H2.  unfold not. intros. simpl in H6.
destruct (string_dec (scenarioId s1) (scenarioId s)).
pose proof  ScenarioEquivalence.
assert (s1 = s). apply H7. auto. exfalso;apply H5;auto.
exfalso;apply H3;auto. 
unfold not. intros. simpl in H6.    
destruct (string_dec (scenarioId s1) (scenarioId s)).
pose proof  ScenarioEquivalence.
assert (s1 = s). apply H7. auto. exfalso;apply H5;auto.
exfalso;apply H4;auto. simpl in H6.  
destruct (string_dec (scenarioId s1) (scenarioId s)). 
 pose proof  ScenarioEquivalence.
assert (s1 = s). apply H7. auto. exfalso;apply H5;auto.
auto.     
Qed. 


Lemma mergeControlStateFuncSym: forall cso cs1 cs2, 
uniqList (dom (cso)) ->
uniqList (dom ( cs1)) ->
uniqList (dom (cs2)) ->
noControlConflict cso cs1 cs2 -> 
mergeControlStateFunc (cso) (cs1) (cs2) =
      mergeControlStateFunc (cso) (cs2) (cs1).
Proof. intro  cso. induction cso.
- intros. simpl. auto.
- intros. simpl. 
destruct a.  
destruct cs1. destruct cs2. auto. destruct p. auto.
destruct cs2. destruct p. auto.  
destruct p. 
destruct p0.   
remember (scenario_dec s s1).
destruct s5. Focus 2. 
destruct (scenario_dec s s3). auto. auto.
 remember (scenario_dec s s3).
destruct s5. Focus 2. auto.
assert (mergeControlStateFunc cso cs1 cs2 = mergeControlStateFunc cso cs2 cs1).
apply IHcso. inversion H. auto. inversion H0;auto. inversion H1;auto.
eapply noControlConf'. apply H. rewrite <-e in H0.   apply H0. rewrite <-e0 in H1. apply H1.    
 rewrite <- e in H2. rewrite <- e0 in H2. auto.   
rewrite H3. 
remember (mergeControlStateFunc cso cs2 cs1).
destruct e1. 
Focus 2.   auto. 
remember (string_dec s2 s4). destruct s5.
rewrite e1. 
destruct (string_dec s4 s4). auto. exfalso;apply n;auto.
remember (string_dec s2 s0).
destruct s5. 
remember (string_dec s4 s2). destruct s5.
auto.    
remember (string_dec s4 s0).
destruct s5.  clear Heqs4.  rewrite <-  e1 in e2. exfalso;apply n;auto. auto. 
 destruct (string_dec s4 s2).
exfalso;apply n;auto. 
destruct (string_dec s4 s0).
auto.    rewrite <- e in H2. rewrite <- e0 in H2. 
unfold noControlConflict in H2. 
assert (getScenarioState s ((s, s2) :: cs1) = getScenarioState s ((s, s4) :: cs2)).
apply H2.   unfold not. intros. simpl in H4.        
destruct (string_dec (scenarioId s) (scenarioId s)). inversion H4. apply n0. auto.  exfalso;apply n3;auto. 
unfold not.  intros. 
simpl in H4.        
destruct (string_dec (scenarioId s) (scenarioId s)). inversion H4. apply n2. auto. exfalso;apply n3;auto.
simpl in H4.  
destruct (string_dec (scenarioId s) (scenarioId s)).
inversion H4. exfalso;apply n;auto. exfalso;apply n3;auto.
Qed. 



Lemma mergeListEquiv': forall (A:Type)  l l' l2 l2' decA, 
uniqList l ->
uniqList l' ->
uniqList l2 ->
uniqList l2' ->
equivList l l' ->
equivList l2 l2' ->
equivList (@mergeList' A l l2' decA) (@mergeList' A l2 l' decA).
Proof. 
intros. generalize dependent l2. generalize dependent l2'.
induction H3.
- intros. unfold mergeList'. simpl.
  rewrite app_nil_r. 
rewrite filterNil.  apply Permutation_sym. auto.
- intros. unfold mergeList'.
simpl.
remember (inList decA x l2). destruct b. 
assert (Permutation (x :: (app l  (filterList (x :: l) l2' decA))) (app l  (filterList (l) l2' decA))).
apply  middleMergeListEquiv. auto. inversion H;auto. auto. 
assert (In x l2). SearchAbout inList. eapply reverseinListLemma. symmetry. apply Heqb. 
eapply Permutation_in. apply H4. auto.  
inversion H;subst. auto. 
assert (Permutation (l ++ filterList l l2' decA)  (l2 ++ filterList l2 l'0 decA)).
unfold mergeList' in IHPermutation.  apply IHPermutation. inversion H; auto. inversion H0;auto. auto. auto.
auto. 
eapply Permutation_trans. apply H5. apply H6.
assert (~In x l2). SearchAbout inList. eapply reverseinListFalse. symmetry. apply Heqb. 
assert (~In x l2'). unfold not. intros. unfold not in H5. apply H5.  eapply Permutation_in.
assert (Permutation l2' l2). apply Permutation_sym. auto. apply H7. auto.               
unfold mergeList' in IHPermutation. 
assert (Permutation (x :: (app l  (filterList (x :: l) l2' decA))%list) (app l (x::(filterList (x :: l) l2' decA))%list)).
apply Permutation_middle. 
Check filterNoEffect.
assert (x::l = (app (x::nil) l)). simpl.
auto.     
assert (filterList (app (x::nil) l) l2' decA = filterList l l2' decA).
apply filterNoEffect. simpl. auto. auto. intros. destruct H9. rewrite <- H9. auto. inversion H9.
rewrite <- H8 in H9. rewrite H9 in H7. 
Check filterNoEffect.
assert (Permutation (app l2 (x :: filterList l2 l'0 decA))  (x::(app l2 (filterList l2 l'0 decA)))). 
apply Permutation_sym. 
apply Permutation_middle. 
assert (Permutation (x :: (l ++ filterList (x :: l) l2' decA)%list)  (x :: (l2 ++ filterList l2 l'0 decA)%list)).
eapply perm_skip. 
rewrite H9. apply IHPermutation. inversion H;auto.  inversion H0;auto. auto. auto. auto. 
eapply perm_trans. apply H11. 
apply Permutation_sym. auto.
- intros. unfold mergeList'. 
simpl.    
remember (inList decA x l2).
destruct b. 
remember (inList decA y l2).
destruct b. inversion H. subst. 
inversion H6. subst. 
assert ((y :: x :: (l ++ filterList (y :: x :: l) l2' decA)%list) = (y :: (app (x :: l) (filterList (y :: (x :: l)) l2' decA))%list)).
simpl. auto.
rewrite H3.
assert (Permutation ((y :: ((x :: l) ++ filterList (y :: x :: l) l2' decA)%list)) (app (x::l) (filterList (x::l) l2' decA)) ).
apply middleMergeListEquiv;auto.  assert (In y l2). SearchAbout inList.  eapply reverseinListLemma.
symmetry. apply Heqb0.
eapply Permutation_in. apply H4. auto. 
eapply perm_trans. apply H5. 
assert (Permutation ((x :: (( l) ++ filterList ( x :: l) l2' decA)%list)) (app (l) (filterList (l) l2' decA)) ).
apply middleMergeListEquiv;auto. 
assert (In x l2). SearchAbout inList.  eapply reverseinListLemma.
symmetry. apply Heqb.
eapply Permutation_in. apply H4. auto.
eapply perm_trans. apply H10. apply mergeListEquivE'. auto. auto. auto. inversion H6;auto. 
assert (Permutation (y::(app l2 (filterList l2 l decA)))  (app l2  (y :: filterList l2 l decA))).
apply Permutation_middle. 
assert (Permutation (y :: x :: (l ++ filterList (y :: x :: l) l2' decA)%list)  (y :: (l2 ++ filterList l2 l decA)%list)).
constructor. 
assert (filterList (y :: x :: l) l2' decA = filterList (x::l) l2' decA).
assert (y::x::l = app (y::nil) (x::l)).
simpl. auto. rewrite H5.    
apply filterNoEffect. simpl. auto. auto. intros. destruct H6. rewrite <- H6. assert (~In y l2). 
  SearchAbout inList. eapply reverseinListFalse. symmetry. apply Heqb0. 
unfold not.  intros. unfold not in H7. apply H7.  
eapply Permutation_in. apply Permutation_sym. eapply H4. auto. 
inversion H6. rewrite H5. 
assert (Permutation (x :: (l ++ filterList (x :: l) l2' decA)%list) (app l (filterList l l2' decA))).
apply middleMergeListEquiv. inversion H. inversion H8;auto. auto. 
assert (In x l2). eapply reverseinListLemma.
symmetry. apply Heqb. eapply Permutation_in. apply H4. auto. inversion H. inversion H8;auto. 
eapply perm_trans. apply H6.   apply mergeListEquivE'. auto. auto. auto. inversion H.  inversion H9;auto.
eapply perm_trans. apply H5. auto. 
remember (inList decA y l2). 
destruct b. 
+ assert (Permutation (y :: x :: (l ++ filterList (y :: x :: l) l2' decA)%list) (x :: y :: (l ++ filterList (y :: x :: l) l2' decA)%list)).
constructor. 
assert (Permutation (l2 ++ x :: filterList l2 l decA) (x:: (app l2  (filterList l2 l decA)))).
apply Permutation_sym. apply Permutation_middle. 
eapply perm_trans. apply H3.
eapply Permutation_sym.
eapply perm_trans. apply H5. 
eapply perm_skip.
assert (~In x l2).
eapply reverseinListFalse. symmetry. apply Heqb.
assert (~In x l2'). 
unfold not. intros. unfold not in H6. apply H6. eapply Permutation_in. 
apply Permutation_sym. apply H4. auto. 
 rewrite filterListSkip. Focus 2. auto. Focus 2. auto.
apply Permutation_sym. 
Check middleMergeListEquiv.
assert (Permutation (y :: (l ++ filterList (y :: l) l2' decA)%list) (app l  (filterList ( l) l2' decA)%list)).  
apply  middleMergeListEquiv. inversion H. inversion H10;auto. auto. assert (In y l2).  eapply reverseinListLemma.
symmetry. apply Heqb0.  eapply Permutation_in. apply H4. auto.  
inversion H0. inversion H10;auto.
eapply perm_trans. apply H8.  apply mergeListEquivE'. auto. auto. auto. inversion H. inversion H11;auto.         
+ rewrite filterListSkip. Focus 2. auto. Focus 2. assert (~In x l2).   
eapply reverseinListFalse. symmetry. apply Heqb. unfold not. intros. unfold not in H3. apply H3.
eapply Permutation_in. apply Permutation_sym. apply H4. auto.
assert (y::l =app  (y::nil) l).
simpl. auto.
rewrite H3. 
rewrite filterNoEffect. Focus 2. simpl. inversion H0;auto. Focus 2. auto. Focus 2. intros. destruct H5.
rewrite <- H5.  assert (~In y l2).   
eapply reverseinListFalse. symmetry. apply Heqb0. unfold not. intros.  unfold not in H6. apply H6. 
eapply Permutation_in. symmetry. apply H4. auto. destruct H5.
assert (Permutation (l2 ++ x :: y :: filterList l2 l decA) (x::(app l2 (y::(filterList l2 l decA))))).
apply Permutation_sym. 
apply Permutation_middle.  
assert (Permutation ((l2 ++ y :: filterList l2 l decA)%list) ((y :: (app l2  (filterList l2 l decA)%list)))).
apply Permutation_sym. 
apply Permutation_middle.
assert (Permutation (x :: (l2 ++ y :: filterList l2 l decA)%list)  (x::(y :: (l2 ++ filterList l2 l decA)%list))).
apply perm_skip.
auto. 
apply Permutation_sym.
eapply perm_trans. apply H5. 
eapply perm_trans. apply H7. 
assert (Permutation  (x :: y :: (l2 ++ filterList l2 l decA)%list)   (y :: x :: (l2 ++ filterList l2 l decA)%list)).
constructor. eapply perm_trans. apply H8.
constructor. constructor. Check  mergeListEquivE'. apply Permutation_sym.   apply mergeListEquivE'.
auto. auto. auto. inversion H. inversion H11. auto.                           

- intros.      
assert (equivList (mergeList' l l2' decA) (mergeList' l2 l'0 decA)).
apply IHPermutation1. auto.     
Focus 2.         
eapply PermuUniq. apply H4. auto. auto.     
eapply PermuUniq. apply H3_. auto. auto. auto. 
assert (equivList (mergeList' l'0 l2' decA) (mergeList' l2 l'' decA)).
apply IHPermutation2. eapply PermuUniq. apply H3_. auto.
eapply PermuUniq. apply H3_0.  
 eapply PermuUniq. apply H3_. auto.
auto. auto. auto. 
eapply perm_trans. apply H3.      
apply mergeListPermu'. auto.   
eapply PermuUniq. apply H3_. auto.    
eapply PermuUniq. apply H3_0. 
eapply PermuUniq. apply H3_. auto.    
auto.  
Qed.              

Definition uniqAllConf (conf:configuration):Prop := uniqList (dom (datastate conf)) /\ uniqList (raisedevents conf)
/\ uniqList (exportedevents conf) /\ uniqList (finishedscenarios conf) /\ uniqList (dom (controlstate conf)).

Lemma mergeConfigEquiv': forall conf conf' conf1 conf2 conf1' conf2' conf3,
equivConf conf conf' ->
equivConf conf1 conf2 ->
equivConf conf1' conf2' ->
Result conf3 = mergeConfigFunc conf conf1 conf1'-> 
uniqAllConf conf ->
uniqAllConf conf' ->
uniqAllConf conf1 ->
uniqAllConf conf2 ->
uniqAllConf conf1' ->
uniqAllConf conf2' ->
noDataConflict (datastate conf) (datastate conf1) (datastate conf1') ->
noControlConflict (controlstate conf) (controlstate conf1) (controlstate conf1') ->
(exists conf3', Result conf3' = mergeConfigFunc conf' conf2' conf2 /\ equivConf conf3 conf3').
Proof. 
intros. unfold equivConf in H.
unfold equivConf in H0.
unfold equivConf in H1.       
unfold mergeConfigFunc.
unfold mergeConfigFunc in H2.
 unfold uniqAllConf in H3. 
 unfold uniqAllConf in H4.  
 unfold uniqAllConf in H5.  
 unfold uniqAllConf in H6.  
 unfold uniqAllConf in H7.  
 unfold uniqAllConf in H8.   
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
rewrite <- H.
rewrite <- H0.
rewrite <- H1.
rewrite <- H43.
rewrite <- H39. 
rewrite <- H35.
pose proof mergeDataStateFuncSym.
assert (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf1') 
= mergeDataStateFunc (datastate conf) (datastate conf1') (datastate conf1)).
apply H47;auto.     
rewrite <- H48. 
 remember (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf1')).
destruct e. Focus 2. inversion H2. 
assert (mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf1') 
= mergeControlStateFunc (controlstate conf) (controlstate conf1') (controlstate conf1)). 
apply mergeControlStateFuncSym;auto.  

rewrite <- H49.  
remember (mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf1') ).
destruct e.
Focus 2. inversion H2.
 exists ({|
    datastate := v;
    controlstate := v0;
    raisedevents := mergeList' (raisedevents conf2') (raisedevents conf2) raisedEvent_dec;
    exportedevents := mergeList' (exportedevents conf2') (exportedevents conf2) raisedEvent_dec;
    finishedscenarios := mergeList' (finishedscenarios conf2') (finishedscenarios conf2) scenario_dec;
    srcstatefinishedscenarios := mergeList' (srcstatefinishedscenarios conf2') (srcstatefinishedscenarios conf2)
                                   scenarioState_dec;
    updatedvariableList := mergeList' (updatedvariableList conf2') (updatedvariableList conf2) updatedVariable_dec;
    usedvariableList := mergeList' (usedvariableList conf2') (usedvariableList conf2) usedVariable_dec |}).
inversion H2. split.
auto.
unfold equivConf;split;simpl. auto.
split. auto.           
 Print mergeList'. 
split.  apply mergeListEquiv'.  auto. auto. auto. auto. auto.  apply Permutation_sym.
 auto. split. 
apply mergeListEquiv'.  auto. auto. auto. auto. auto.  apply Permutation_sym.
 auto. 
apply mergeListEquiv'.  auto. auto. auto. auto. auto.  apply Permutation_sym.
 auto.
Qed. 
  

Lemma innerCombineEquiv': forall conf conf' lst conf1,
equivConf conf conf' ->
Result conf1 =  innerCombineFunc' conf None lst ->
uniqList (dom (datastate conf)) ->
uniqList (dom (datastate conf')) ->
uniqList (raisedevents conf) ->
uniqList (raisedevents conf') ->
uniqList (exportedevents conf) ->
uniqList (exportedevents conf') ->
uniqList (finishedscenarios conf) ->
uniqList (finishedscenarios conf') ->
uniqList (dom (controlstate conf)) ->
uniqList (dom (controlstate conf')) ->
(forall conf2, In conf2 lst -> 
 uniqList (dom (datastate conf2)) /\
 uniqList (raisedevents conf2) /\ 
 uniqList (exportedevents conf2) /\
 uniqList (finishedscenarios conf2) /\
 uniqList (dom (controlstate conf2))
) ->
(forall conf2 conf2', In conf2 lst -> In conf2' lst ->
noDataConflict (datastate conf) (datastate conf2) (datastate conf2')  /\ 
noControlConflict (controlstate conf) (controlstate conf2) (controlstate conf2')
) ->
(exists conf2, Result conf2 =  innerCombineFunc' conf' None lst /\
equivConf conf1 conf2).
Proof.
intros. generalize dependent conf. generalize dependent conf'.
generalize dependent conf1. induction lst.
- intros. simpl. simpl in H0. inversion H0.
- intros.       
simpl in H0. simpl. destruct lst. simpl. simpl in H0.
inversion H0. exists a. split;auto. eapply equivConf_Refl.
simpl in H0.           
remember (innerCombineFunc' conf (Some c) lst).
destruct e. Focus 2. inversion H0.
simpl.      
remember Heqe. clear Heqe0. apply IHlst with (conf':=conf') in e. 
destruct e. destruct H13.   simpl in H13. rewrite<- H13. 
pose proof mergeConfigEquiv. remember H0. clear Heqe0.  
apply H15 with (conf:=conf) (conf1:=a) (conf1':=v);auto.   SearchAbout equivConf. apply equivConf_Refl.
intros. apply H11. right;auto. auto. auto.  auto. auto. auto. auto. auto. auto. auto. auto. auto.
intros. apply H12. right;auto. right;auto.
Qed.                  






(*switch parameter order in mergeConfigFunc will not influence the result*)
Lemma mergeConfSwitchInvariant: forall conf conf1 conf2 conf3,
Result conf3 = mergeConfigFunc conf conf1 conf2   ->
uniqAllConf (conf) ->
uniqAllConf (conf1) ->
uniqAllConf (conf2) ->
uniqList (dom (datastate conf)) ->
noDataConflict (datastate conf) (datastate conf1) (datastate conf2) ->
noControlConflict (controlstate conf) (controlstate conf1) (controlstate conf2) ->
(exists conf3', Result conf3' = mergeConfigFunc conf conf2 conf1 /\ equivConf conf3 conf3').
Proof. intros.
unfold  mergeConfigFunc in H.
unfold  mergeConfigFunc.
unfold uniqAllConf in H0.  
unfold uniqAllConf in H1.  
unfold uniqAllConf in H2.  
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. 
SearchAbout mergeDataStateFunc.
assert  (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2) = 
 mergeDataStateFunc (datastate conf) (datastate conf2) (datastate conf1)).
 SearchAbout mergeDataStateFunc.
apply  mergeDataStateFuncSym;auto.
rewrite <- H18. 
destruct (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2)).
Focus 2. inversion H.
SearchAbout mergeControlStateFunc. 
(*mergeControlStateFuncSym*) 
assert (mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf2) 
            = mergeControlStateFunc (controlstate conf) (controlstate conf2) (controlstate conf1)).
apply  mergeControlStateFuncSym;auto.
rewrite <- H19.
destruct (mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf2)). Focus 2. 
inversion H.
SearchAbout  mergeList'.         
exists ( {|
    datastate := v;
    controlstate := v0;
    raisedevents := mergeList' (raisedevents conf2) (raisedevents conf1) raisedEvent_dec;
    exportedevents := mergeList' (exportedevents conf2) (exportedevents conf1) raisedEvent_dec;
    finishedscenarios := mergeList' (finishedscenarios conf2) (finishedscenarios conf1) scenario_dec;
    srcstatefinishedscenarios := mergeList' (srcstatefinishedscenarios conf2) (srcstatefinishedscenarios conf1)
                                   scenarioState_dec;
    updatedvariableList := mergeList' (updatedvariableList conf2) (updatedvariableList conf1) updatedVariable_dec;
    usedvariableList := mergeList' (usedvariableList conf2) (usedvariableList conf1) usedVariable_dec |}).
split;auto.
inversion H.    
unfold equivConf;split;simpl;auto. split;auto.
split. 
SearchAbout mergeList'. 
apply mergeListSymEquiv;auto.
split;apply mergeListSymEquiv;auto.
Qed.      

(*switch parameter order in mergeConfigFunc will not influence the result*)
Lemma mergeConfSwitchInvariant': forall conf conf' conf1 conf2 conf3,
Result conf3 = mergeConfigFunc conf conf1 conf2   ->
uniqAllConf (conf) ->
uniqAllConf (conf1) ->
uniqAllConf (conf2) ->
uniqList (dom (datastate conf)) ->
noDataConflict (datastate conf) (datastate conf1) (datastate conf2) ->
noControlConflict (controlstate conf) (controlstate conf1) (controlstate conf2) ->
equivConf conf conf' -> 
(exists conf3', Result conf3' = mergeConfigFunc conf' conf2 conf1 /\ equivConf conf3 conf3').
Proof.
intros.
unfold  mergeConfigFunc in H.
unfold  mergeConfigFunc.
unfold uniqAllConf in H0.  
unfold uniqAllConf in H1.  
unfold uniqAllConf in H2.  
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. 
SearchAbout mergeDataStateFunc.
assert  (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2) = 
 mergeDataStateFunc (datastate conf) (datastate conf2) (datastate conf1)).
 SearchAbout mergeDataStateFunc.
apply  mergeDataStateFuncSym;auto.
unfold equivConf in H6. destruct H6.
rewrite <- H6.   
rewrite <- H19. 
destruct (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2)).
Focus 2. inversion H.
SearchAbout mergeControlStateFunc. 
(*mergeControlStateFuncSym*) 
assert (mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf2) 
            = mergeControlStateFunc (controlstate conf) (controlstate conf2) (controlstate conf1)).
apply  mergeControlStateFuncSym;auto.
destruct H20.
rewrite <- H20.  
rewrite <- H21.
destruct (mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf2)). Focus 2. 
inversion H.
SearchAbout  mergeList'.         
exists ( {|
    datastate := v;
    controlstate := v0;
    raisedevents := mergeList' (raisedevents conf2) (raisedevents conf1) raisedEvent_dec;
    exportedevents := mergeList' (exportedevents conf2) (exportedevents conf1) raisedEvent_dec;
    finishedscenarios := mergeList' (finishedscenarios conf2) (finishedscenarios conf1) scenario_dec;
    srcstatefinishedscenarios := mergeList' (srcstatefinishedscenarios conf2) (srcstatefinishedscenarios conf1)
                                   scenarioState_dec;
    updatedvariableList := mergeList' (updatedvariableList conf2) (updatedvariableList conf1) updatedVariable_dec;
    usedvariableList := mergeList' (usedvariableList conf2) (usedvariableList conf1) usedVariable_dec |}).
split;auto.
inversion H.    
unfold equivConf;split;simpl;auto. split;auto.
split. 
SearchAbout mergeList'. 
apply mergeListSymEquiv;auto.
split;apply mergeListSymEquiv;auto.
Qed. 

(*switch parameter order in mergeConfigFunc will not influence the result*)
Lemma mergeConfSwitchInvariant'': forall conf conf' conf1 conf2 conf3 conf1' conf2',
Result conf3 = mergeConfigFunc conf conf1 conf2   ->
uniqAllConf (conf) ->
uniqAllConf (conf1) ->
uniqAllConf (conf2) ->
uniqAllConf (conf1') ->
uniqAllConf (conf2') ->
uniqList (dom (datastate conf)) ->
noDataConflict (datastate conf) (datastate conf1) (datastate conf2) ->
noControlConflict (controlstate conf) (controlstate conf1) (controlstate conf2) ->
noDataConflict (datastate conf') (datastate conf1') (datastate conf2') ->
noControlConflict (controlstate conf') (controlstate conf1') (controlstate conf2') ->
equivConf conf conf' -> 
equivConf conf1 conf1' ->
equivConf conf2 conf2' ->
(exists conf3', Result conf3' = mergeConfigFunc conf' conf2' conf1' /\ equivConf conf3 conf3').
Proof. 
  intros.
unfold  mergeConfigFunc in H.
unfold  mergeConfigFunc.
unfold uniqAllConf in H0.  
unfold uniqAllConf in H1.  
unfold uniqAllConf in H2.  
unfold uniqAllConf in H3.  
unfold uniqAllConf in H4.  
unfold uniqAllConf in H5.  
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.  
SearchAbout mergeDataStateFunc.
assert  (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2) = 
 mergeDataStateFunc (datastate conf) (datastate conf2) (datastate conf1)).
 SearchAbout mergeDataStateFunc.
apply  mergeDataStateFuncSym;auto.
unfold equivConf in H10. destruct H10.
rewrite <- H10.
unfold equivConf in H11. destruct H11.
rewrite <- H11.
unfold equivConf in H12. destruct H12.
rewrite <- H12.  
rewrite <- H33. 
destruct (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2)).
Focus 2. inversion H.
SearchAbout mergeControlStateFunc. 
(*mergeControlStateFuncSym*) 
assert (mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf2) 
            = mergeControlStateFunc (controlstate conf) (controlstate conf2) (controlstate conf1)).
apply  mergeControlStateFuncSym;auto.
destruct H36.
rewrite <- H36.
destruct H35.
rewrite <- H35. 
destruct H34.
rewrite <- H34. 
  
rewrite <- H37.
destruct (mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf2)). Focus 2. 
inversion H.
SearchAbout  mergeList'.         
exists ({|
    datastate := v;
    controlstate := v0;
    raisedevents := mergeList' (raisedevents conf2') (raisedevents conf1') raisedEvent_dec;
    exportedevents := mergeList' (exportedevents conf2') (exportedevents conf1') raisedEvent_dec;
    finishedscenarios := mergeList' (finishedscenarios conf2') (finishedscenarios conf1') scenario_dec;
    srcstatefinishedscenarios := mergeList' (srcstatefinishedscenarios conf2')
                                   (srcstatefinishedscenarios conf1') scenarioState_dec;
    updatedvariableList := mergeList' (updatedvariableList conf2') (updatedvariableList conf1')
                             updatedVariable_dec;
    usedvariableList := mergeList' (usedvariableList conf2') (usedvariableList conf1') usedVariable_dec |}).
split;auto.
inversion H.    
unfold equivConf;split;simpl;auto. split;auto.
split. 
SearchAbout mergeList'. 
apply mergeListEquiv';auto. destruct H39;auto. destruct H38;auto. apply Permutation_sym;auto.
split. 
SearchAbout mergeList'. 
apply mergeListEquiv';auto.  destruct H39;auto. destruct H41;auto.  destruct H38;auto. destruct H41;apply Permutation_sym;auto.
apply mergeListEquiv';auto.  destruct H39;auto. destruct H41;auto.   destruct H38;auto. destruct H41;apply Permutation_sym;auto.
Qed. 

(*merge order does not matter*)
Lemma mergeDataStateFuncEquivOnCom': forall (dso  x y v0 v1 v2: list (atom * (typ * range_typ))), 
uniqList (dom (dso)) ->
(dom (dso) = dom(x)) ->
(dom (dso) = dom (y)) ->
(dom (dso) = dom (v0)) ->
noDataConflict dso x v0 ->
noDataConflict dso y v1 ->
Result v1 = mergeDataStateFunc dso x v0 ->
Result v2 = mergeDataStateFunc dso y v1 ->
(exists v1' v2',
Result v1' = mergeDataStateFunc dso y v0 /\
Result v2' = mergeDataStateFunc dso x v1' /\
v2 = v2').
Proof. intro dso. induction (dso).  
- intros.  simpl. simpl in H5. inversion H5.
- intros. simpl in H5.  
destruct a. destruct p. 
destruct x. inversion H5.
destruct p. destruct p.  
destruct v0. inversion H5.  
destruct p. destruct p. 
remember (atom_eq_dec a a0) . 
destruct s. Focus 2. inversion H5.
 remember (atom_eq_dec a a1). destruct s. Focus 2. inversion H5. 
  remember (typ_eq_dec t t0). destruct s. Focus 2. inversion H5.
  destruct (typ_eq_dec t t1). Focus 2. inversion H5.
 remember (mergeDataStateFunc l x v0).
destruct e3. Focus 2. inversion H5. 
destruct (range_typ_dec r0 r1). 
inversion H5.  rewrite H8 in H6.
rewrite <- e3. rewrite <- e. rewrite <-e0.
simpl. destruct y. simpl in H6. inversion H6. 
simpl in H6.
destruct p. destruct p.  
destruct (atom_eq_dec a a2). Focus 2. inversion H6.
destruct (atom_eq_dec a a). Focus 2. inversion H6.
 destruct (typ_eq_dec t t2). Focus 2. inversion H6.
 destruct (typ_eq_dec t t). Focus 2. inversion H6.
remember (mergeDataStateFunc l y v).
destruct e8. Focus 2.  inversion H6.
destruct (range_typ_dec r2 r0).  
+   destruct (typ_eq_dec t t1). Focus 2. exfalso;apply n;auto. 
subst.              
rewrite <- e0 in H3.         
rewrite <- e2 in H3.   
remember (mergeDataStateFunc l y v0). 
destruct e. exists ( ((a0, (t0, r1)) :: v1)). 
destruct  (atom_eq_dec a0 a0). destruct (typ_eq_dec t0 t0). Focus 2. exfalso;apply n;auto.  Focus 2. 
exfalso; apply n;auto. 
remember (mergeDataStateFunc l x v1 ).
destruct e3.   
 destruct (range_typ_dec r1 r1). Focus 2. exfalso;apply n;auto. 
exists ((a0, (t0, r1)) :: v4). split;auto. split;auto.
inversion H6. f_equal.  
apply IHl with (x:=x) (v0:=v0) in Heqe8.  
destruct Heqe8.
destruct H7. destruct H7. destruct H9.
rewrite <- H7 in Heqe.  inversion Heqe. rewrite  H12 in Heqe0. 
rewrite <- H9 in Heqe0. inversion Heqe0. auto. 
inversion H. auto. auto. inversion H0. auto. inversion H1. auto.  inversion H2. auto.
SearchAbout noDataConflict.          
eapply noDataConf'. apply H. rewrite  H0 in H.  apply H.  rewrite H2 in H. rewrite <- e0 in H.
rewrite <- e9 in H.   apply H. auto. 
eapply noDataConf'. apply H. rewrite H1 in H. rewrite <- e4 in H. rewrite <-e6 in H. apply H.
assert (uniqList ((dom ((a0, (t0, r1)) :: v)))). 
Print mergeDataStateFunc.  
inversion H2. inversion H0. inversion H1. simpl. constructor.  eapply mergeDataStateUniqInvariant.
inversion H. apply H15. apply H11. apply H10. auto. 
assert (dom v = dom l). eapply mergeDataStateUniqInvariant'. apply H11. apply H10. auto.
rewrite H7. inversion H;subst. auto.                      
apply H7. auto. rewrite <- e6 in H4. auto. rewrite <-e4 in H4. auto.  auto. 
SearchAbout mergeDataStateFunc. 
inversion H2. subst. 
inversion H;subst. apply IHl with (v0:=v0) (x:=x) in Heqe8.  Focus 2. inversion H;auto.  Focus 2. inversion H0. auto. Focus 2. inversion H1. auto.
Focus 2. inversion H2. auto.  Focus 2. SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H. apply H. apply H3. 
Focus 2. SearchAbout  noDataConflict. eapply noDataConf'. apply H. rewrite H1 in H. apply H. Focus 2. apply H4.
simpl. constructor.  assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'. 
inversion H0. apply H10.  inversion H2. apply H10.  auto. rewrite H7. inversion H;auto. 
assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'. 
inversion H0. apply H10.    inversion H2. apply H10.  auto. rewrite H7. inversion H;auto.             
Focus 2. auto. destruct Heqe8. destruct H7. destruct H7. destruct H10.  rewrite <- Heqe in H7. 
inversion H7. subst. rewrite <- H10 in Heqe0. inversion Heqe0.        
apply IHl with (v0:=v0) (x:=x) in Heqe8.  Focus 2. inversion H;auto.  Focus 2. inversion H0. auto. Focus 2. inversion H1. auto.
Focus 2. inversion H2. auto.  Focus 2. SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H. rewrite <- e0 in H. rewrite <- e2 in H.   apply H. apply H3.
 
Focus 2. SearchAbout  noDataConflict. eapply noDataConf'. apply H. rewrite H1 in H. rewrite <- e4 in H. rewrite <- e6 in H. 
 apply H. simpl. constructor.    assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
inversion H0. apply H8.    inversion H2. apply H9. auto. rewrite H7. inversion H;auto. 
assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'. inversion H0. apply H8. 
inversion H2. apply H9. auto. rewrite H7. inversion H;auto.         

  rewrite <- e4 in H4. rewrite <- e6 in H4.   apply H4.
destruct Heqe8. destruct H7. destruct H7. destruct H8.   rewrite <- H7 in Heqe.  inversion Heqe. auto. 
+ 
destruct (typ_eq_dec t t1). Focus 2.    
destruct ( range_typ_dec r2 r). 
Print noDataConflict. exfalso;apply n0;auto. exfalso;apply n0;auto.   
destruct (range_typ_dec r2 r).  
remember (mergeDataStateFunc l y v0).
destruct e10. 
exists (((a, (t, r0)) :: v4)). 
destruct (atom_eq_dec a a). 
Focus 2. exfalso;apply n0. auto.
destruct (typ_eq_dec t t0).
Focus 2.  exfalso;apply n0;auto.
 destruct (typ_eq_dec t t).
Focus 2. exfalso;apply n0;auto. 
remember (mergeDataStateFunc l x v4).
destruct e13. 
destruct (range_typ_dec r0 r0). Focus 2. exfalso;apply n0;auto. 
exists (((a, (t, r0)) :: v5)). split;auto. split;auto.  inversion H6. 
f_equal.
apply IHl with (x:=x) (v0:=v0) in Heqe8.  
destruct Heqe8.
destruct H7. destruct H7. destruct H10. 
rewrite <- H7 in Heqe10.  inversion Heqe10. rewrite  H13 in Heqe13. 
rewrite <- H10 in Heqe13.  inversion Heqe13.  auto. 
inversion H. auto. auto. inversion H0. auto. inversion H1. auto.  inversion H2. auto.                   
SearchAbout noDataConflict.          
eapply noDataConf'. apply H. rewrite  H0 in H. rewrite e1. rewrite e.    apply H.  rewrite H2 in H. rewrite <- e0 in H.
rewrite e2.  apply H. rewrite <- e in H3. rewrite <- e0 in H3. auto.     
eapply noDataConf'. apply H. rewrite H1 in H. rewrite e4. rewrite e6. apply H.
 rewrite H8 in H4. 
simpl.  constructor.  assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
inversion H0. apply H11. inversion H2. apply H11. auto. rewrite H7. inversion H;auto. 
assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'. 
 inversion H0. apply H11. inversion H2. apply H11. auto. rewrite H7. inversion H;auto.     
rewrite H8 in H4. 
rewrite <- e4 in H4. rewrite <- e6 in H4. apply H4. auto. subst. 
apply IHl with (v0:=v0) (x:=x) in Heqe8.  Focus 2. inversion H;auto.  Focus 2. inversion H0. auto. Focus 2. inversion H1. auto.
Focus 2. inversion H2. auto.  Focus 2. SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H. rewrite <- e0 in H. rewrite <- e2 in H.   apply H. rewrite <- e0 in H3.
rewrite <- e8 in H3.   apply H3.
 
Focus 2. SearchAbout  noDataConflict. eapply noDataConf'. apply H. rewrite H1 in H. rewrite <- e4 in H. rewrite <- e6 in H. 
 apply H. 
simpl.  

constructor.    assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
 inversion H0. apply H8. inversion H2. apply H9. auto. rewrite H7. inversion H;auto. 
assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
 inversion H0. apply H8. inversion H2. apply H9. auto. rewrite H7. inversion H;auto.     
 rewrite <- e4 in H4. rewrite <- e6 in H4.   apply H4.
Focus 2. auto. destruct Heqe8. destruct H7. destruct H7. destruct H8.   rewrite <- H7 in Heqe10.  inversion Heqe10.
rewrite <- H11 in H8. rewrite <- H8 in Heqe13. inversion Heqe13.
subst.  

apply IHl with (v0:=v0) (x:=x) in Heqe8.  Focus 2. inversion H;auto.  Focus 2. inversion H0. auto. Focus 2. inversion H1. auto.
Focus 2. inversion H2. auto.  Focus 2. SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H. rewrite <- e0 in H. rewrite <- e2 in H.   apply H. rewrite <- e0 in H3.
rewrite <- e8 in H3.   apply H3.
 
Focus 2. SearchAbout  noDataConflict. eapply noDataConf'. apply H. rewrite H1 in H. rewrite <- e4 in H. rewrite <- e6 in H. 
 apply H. 

simpl. constructor.    assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
 inversion H0. apply H8. inversion H2. apply H9. auto. rewrite H7. inversion H;auto. 
assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
 inversion H0. apply H8. inversion H2. apply H9. auto. rewrite H7. inversion H;auto.      
  rewrite <- e4 in H4. rewrite <- e6 in H4.   apply H4.
Focus 2. auto. destruct Heqe8. destruct H7. destruct H7. destruct H8.   rewrite <- H7 in Heqe10.  inversion Heqe10.
remember (mergeDataStateFunc l y v0).
destruct e9.
exists ((a, (t, r2)) :: v4).
destruct (atom_eq_dec a a).
Focus 2. exfalso;apply n1;auto. 
destruct (typ_eq_dec t t0). 
Focus 2. exfalso;apply n1;auto.
destruct (typ_eq_dec t t).
Focus 2. exfalso;apply n1;auto. 
remember (mergeDataStateFunc l x v4).
destruct e12. 
destruct (range_typ_dec r0 r2).
exfalso;apply n;auto.  
 destruct (range_typ_dec r0 r). 
exists (((a, (t, r2)) :: v5)). 
split;auto. split;auto. inversion H6. f_equal.
 subst. clear e11.  clear e7.  clear Heqs. clear Heqs0. clear e5. clear e9. clear Heqs1.   clear e10.
clear n. clear e8.         
apply IHl with (v0:=v0) (x:=x) in Heqe8.  Focus 2. inversion H;auto.  Focus 2. inversion H0. auto. Focus 2. inversion H1. auto.
Focus 2. inversion H2. auto.  Focus 2. SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H. rewrite <- e0 in H. rewrite <- e2 in H.   apply H. rewrite <- e0 in H3.
 apply H3.
 
Focus 2. SearchAbout  noDataConflict. eapply noDataConf'. apply H. rewrite H1 in H. rewrite <- e4 in H. rewrite <- e6 in H. 
 apply H.  

simpl. constructor.    assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
inversion H0. apply H8. inversion H2. apply H9. auto. rewrite H7. inversion H;auto. 
assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
  inversion H0. apply H8. inversion H2. apply H9. auto. rewrite H7. inversion H;auto.     
 rewrite <- e4 in H4. rewrite <- e6 in H4.   apply H4.
Focus 2. auto. destruct Heqe8. destruct H7. destruct H7. destruct H8.   rewrite <- H7 in Heqe9.  inversion Heqe9.  
rewrite <- H11 in H8.  rewrite <- H8 in Heqe12. inversion Heqe12. auto.            
exists (((a, (t, r0)) :: v5)). split;auto. split;auto. inversion H6. simpl. subst.
unfold noDataConflict in H4. rewrite e4 in H4.  rewrite e6 in H4. destruct H4 with a2.
assert (getValue a2 ((a2, (t2, r2)) :: y) = getValue a2 ((a2, (t2, r1)) :: v)).
apply H8. split. unfold not. intros.  simpl in H9. destruct a2;inversion H7. inversion H10. inversion H10. 
destruct (atom_eq_dec (AIdent s) (AIdent s)). inversion H9. exfalso;apply n0;auto. exfalso;apply n3;auto. inversion H10. 
inversion H10. inversion H10. unfold not. intros. simpl in H9.

destruct a2;inversion H7. inversion H10. inversion H10. 
destruct (atom_eq_dec (AIdent s) (AIdent s)). inversion H9. exfalso;apply n2;auto. exfalso;apply n3;auto. inversion H10. 
inversion H10. inversion H10.  simpl in H9. destruct a2;inversion H7. inversion H10. inversion H10. 
destruct (atom_eq_dec (AIdent s) (AIdent s)). inversion H9. exfalso;apply n1;auto. exfalso;apply n3;auto. inversion H10. 
inversion H10. inversion H10. 

                        
  
(*prove by contradiction using noDataConflict*) 
subst. 
apply IHl with (v0:=v0) (x:=x) in Heqe8.  Focus 2. inversion H;auto.  Focus 2. inversion H0. auto. Focus 2. inversion H1. auto.
Focus 2. inversion H2. auto.  Focus 2. SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H. rewrite <- e0 in H. rewrite <- e2 in H.   apply H. rewrite <- e0 in H3.
 apply H3. Focus 2. SearchAbout  noDataConflict. eapply noDataConf'. apply H. rewrite H1 in H. rewrite <- e4 in H. rewrite <- e6 in H. 
 apply H. 
simpl. 
 

simpl. constructor.    assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
 inversion H0. apply H8. inversion H2. apply H9. auto. rewrite H7. inversion H;auto. 
assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
  inversion H0. apply H8. inversion H2. apply H9. auto. rewrite H7. inversion H;auto.   
 rewrite <- e4 in H4. rewrite <- e6 in H4.   apply H4.
Focus 2 . auto. 
destruct Heqe8. destruct H7. destruct H7. destruct H8. subst.     rewrite <- H7 in Heqe9.  inversion Heqe9.  
rewrite <- H10 in H8.  rewrite <- H8 in Heqe12. inversion Heqe12. 

subst. apply IHl with (v0:=v0) (x:=x) in Heqe8.  Focus 2. inversion H;auto.  Focus 2. inversion H0. auto. Focus 2. inversion H1. auto.
Focus 2. inversion H2. auto.  Focus 2. SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H. rewrite <- e0 in H. rewrite <- e2 in H.   apply H. rewrite <- e0 in H3.
 apply H3. Focus 2. SearchAbout  noDataConflict. eapply noDataConf'. apply H. rewrite H1 in H. rewrite <- e4 in H. rewrite <- e6 in H. 
 apply H. 

simpl.  

simpl. constructor.    assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
 inversion H0. apply H8. inversion H2. apply H9. auto. rewrite H7. inversion H;auto. 
assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
  inversion H0. apply H8. inversion H2. apply H9. auto. rewrite H7. inversion H;auto.   
  rewrite <- e4 in H4. rewrite <- e6 in H4.   apply H4.
Focus 2 . auto. 
destruct Heqe8. destruct H7. destruct H7. destruct H8. subst.     rewrite <- H7 in Heqe9.  inversion Heqe9.  
+  destruct (range_typ_dec r0 r ). 
destruct y. inversion H1. subst. destruct v1. inversion H5. 
  destruct p. subst. destruct p. subst. destruct p0;auto. 
simpl.
simpl in H6. 
  
destruct (atom_eq_dec a1 a). Focus 2. destruct p. inversion H6.
destruct (atom_eq_dec a1 a1). Focus 2.  exfalso;apply n0;auto. 
destruct (typ_eq_dec t1 t). Focus 2.  
destruct (atom_eq_dec a1 a0). destruct p.  inversion H6. destruct p. inversion H6. 
destruct (typ_eq_dec t1 t1). Focus 2. exfalso;apply n0;auto.   
destruct (atom_eq_dec a1 a0). Focus 2. destruct p. inversion H6. subst. destruct p.   
destruct (typ_eq_dec t t0). Focus 2. inversion H6. 
remember (mergeDataStateFunc l y v1).
destruct e1.  Focus 2.  inversion H6.
destruct (range_typ_dec r0 r2). subst.  
remember (mergeDataStateFunc l y v0 ).
destruct (range_typ_dec r2 r1).    
destruct e.             
exists ((a0, (t0, r2)) :: v4).  
destruct (atom_eq_dec a0 a0). 
Focus 2.  exfalso;apply n0;auto. 
destruct ( typ_eq_dec t0 t0).
Focus 2. exfalso;apply n0;auto.
remember (mergeDataStateFunc l x v4 ).
destruct e4. 
destruct (range_typ_dec r r2). 
exists (((a0, (t0, r)) :: v5)). split;auto. split;auto. 
inversion H6. rewrite e4.
f_equal.  

rewrite e1 in e4. exfalso;apply n;auto.  
 (*same as the previous proof *)
destruct (range_typ_dec r r). Focus 2. exfalso;apply n1;auto. 
exists ((a0, (t0, r2)) :: v5). split;auto. split;auto. inversion H6. 
f_equal.

apply  IHl  with (x:=x) (v0:=v0) in Heqe1. 
destruct Heqe1. destruct H7. destruct H7. rewrite <- H7 in Heqe;inversion Heqe. rewrite H11 in Heqe4.
destruct H9. rewrite <- H9 in Heqe4. inversion Heqe4. auto.     
 inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H.  apply H. apply H3.  
eapply noDataConf'. apply H. rewrite H1 in H.
 apply H. simpl. 
 constructor.    assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
 inversion H0. apply H9. inversion H2. apply H9. auto. inversion H5.   rewrite H7. inversion H;auto. 
assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
 inversion H0. apply H9. inversion H2. apply H9. auto. inversion H5.  rewrite H7. inversion H;auto.   
  apply H4.  inversion H5. subst. auto.

apply  IHl  with (x:=x) (v0:=v0) in Heqe1. 
destruct Heqe1. destruct H7. destruct H7. rewrite <- H7 in Heqe;inversion Heqe. rewrite H10 in Heqe4.
destruct H8. rewrite <- H8 in Heqe4. inversion Heqe4. auto.     
 inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H.  apply H. apply H3.  
eapply noDataConf'. apply H. rewrite H1 in H.
 apply H. simpl. 
 constructor.    assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
 inversion H0. apply H8. inversion H2. apply H8. auto. inversion H5.   rewrite H7. inversion H;auto. 
assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
  inversion H0. apply H8. inversion H2. apply H8. auto. inversion H5.  rewrite H7. inversion H;auto.   
  apply H4.  inversion H5. subst. auto.
apply  IHl  with (x:=x) (v0:=v0) in Heqe1. 
destruct Heqe1. destruct H7. destruct H7. rewrite <- H7 in Heqe;inversion Heqe. inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H.  apply H. apply H3.  
eapply noDataConf'. apply H. rewrite H1 in H.
 apply H.  

simpl. constructor.    assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
 inversion H0. apply H8. inversion H2. apply H8. auto. inversion H5.   rewrite H7. inversion H;auto. 
assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
inversion H0. apply H8. inversion H2. apply H8. auto. inversion H5.  rewrite H7. inversion H;auto.  
 apply H4.  inversion H5. subst. auto.
destruct (range_typ_dec r2 r). 
destruct e. exists ((a0, (t0, r1)) :: v4). 
destruct (atom_eq_dec a0 a0). 
Focus 2. exfalso;apply n1;auto. 
destruct (typ_eq_dec t0 t0). Focus 2. exfalso;apply n1;auto. 
remember (mergeDataStateFunc l x v4 ). destruct e4. 
 destruct (range_typ_dec r r1). 
exists ((a0, (t0, r)) :: v5).
split;auto. split;auto. inversion H6.
rewrite e1.        
apply IHl with (v0:=v0) (x:=x) in Heqe1.  Focus 2. inversion H;auto.  Focus 2. inversion H0. auto. Focus 2. inversion H1. auto.
Focus 2. inversion H2. auto.  Focus 2. SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H. apply H. apply H3.  Focus 2. SearchAbout  noDataConflict. eapply noDataConf'.
 apply H. rewrite H1 in H. 
 apply H. simpl. constructor.  inversion H5. 
    eapply mergeDataStateUniqInvariant. inversion H. apply H12.

inversion H0. apply H11. inversion H2. apply H11. auto. inversion H. subst. exfalso;apply n0;auto.  apply H4.
Focus 2 .  inversion H5;subst.  auto. destruct Heqe1. subst. exfalso;apply n0;auto. 

destruct (range_typ_dec r r). Focus 2. exfalso;apply n2;auto. 
exists  ((a0, (t0, r1)) :: v5). split;auto. split;auto.
inversion H6.
inversion H5. exfalso;apply n0;auto.  
apply  IHl  with (x:=x) (v0:=v0) in Heqe1. 
destruct Heqe1. destruct H7. destruct H7. rewrite <- H7 in Heqe;inversion Heqe. rewrite  H10 in Heqe4.
destruct H8. rewrite <- Heqe4 in H8. inversion H8.     inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H.  apply H. apply H3.  
eapply noDataConf'. apply H. rewrite H1 in H.
 apply H. 

simpl. constructor.    assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
 inversion H0. apply H8. inversion H2. apply H8. auto. inversion H5.   rewrite H7. inversion H;auto. 
assert (dom v = dom l).  eapply mergeDataStateUniqInvariant'.
 inversion H0. apply H8. inversion H2. apply H8. auto. inversion H5.  rewrite H7. inversion H;auto.  
apply H4.  inversion H5. subst.  exfalso;apply n0;auto.  

apply  IHl  with (x:=x) (v0:=v0) in Heqe1. 
destruct Heqe1. destruct H7. destruct H7. rewrite <- H7 in Heqe;inversion Heqe. inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H.  apply H. apply H3.  
eapply noDataConf'. apply H. rewrite H1 in H.
 apply H. simpl. constructor. inversion H5;subst. exfalso;apply n0;auto.
inversion H5;subst. exfalso;apply n0;auto. apply H4.   inversion H5. subst.   exfalso;apply n0;auto.
destruct e.   inversion H5;subst.  exfalso;apply n0;auto.
inversion H5;subst. exfalso;apply n0;auto. 
remember (mergeDataStateFunc l y v0). 
destruct e1. 
destruct (range_typ_dec r0 r).   
destruct (range_typ_dec r0 r1). rewrite e1 in e4. exfalso;apply n;auto. 
exists ((a, (t, r1)) :: v4).  
destruct (atom_eq_dec a a). Focus 2. exfalso;apply n2;auto. 
destruct (typ_eq_dec t t). Focus 2. exfalso;apply n2;auto. 
remember (mergeDataStateFunc l x v4).
destruct e6. 
destruct (range_typ_dec r r1).   inversion H5. rewrite <- e6 in H10. rewrite e1 in n0.  exfalso;apply n0;auto.
destruct (range_typ_dec r r). Focus 2. exfalso;apply n3;auto.  clear e6.  exists ((a, (t, r1)) :: v5).
split;auto. split;auto. inversion H6.  inversion H5. f_equal. 

 apply  IHl  with (x:=x) (v0:=v0) in Heqe1. 
destruct Heqe1. destruct H7. destruct H7. rewrite <- H7 in Heqe0.  inversion Heqe0. rewrite H15 in Heqe6.
destruct H13. rewrite <- H13 in Heqe6. inversion Heqe6. auto.     
 inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H.  apply H. apply H3.  
eapply noDataConf'. apply H. rewrite H1 in H.
 apply H. simpl. constructor. rewrite H12.   
eapply mergeDataStateUniqInvariant.  inversion H. apply H14. inversion H0. apply H13. inversion H2. apply H13.
auto.  inversion H. simpl in H1.   
assert (dom v = dom l). eapply mergeDataStateUniqInvariant'. inversion H0.
apply H17. inversion H2. apply H17. auto. inversion H2. 
rewrite <- H16 in H18. rewrite H2 in H. inversion H. rewrite H12. rewrite H18. auto. 
rewrite <- H9. rewrite <- H9 in H4.   apply H4. rewrite H12. auto. 

apply  IHl  with (x:=x) (v0:=v0) in Heqe1. 
destruct Heqe1. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe0. inversion Heqe0.
rewrite H11 in Heqe6. rewrite <- H8 in Heqe6.  inversion Heqe6.     inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H.  apply H. apply H3.  
eapply noDataConf'. apply H. rewrite H1 in H.
 apply H. simpl. constructor. inversion H. assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0. apply H12.  
 inversion H2. apply H12. auto. inversion H5.  rewrite H11. auto. 
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0.  apply H8.  
 inversion H2. apply H8. auto.  inversion H5.  rewrite H7. inversion H.  auto. rewrite <- e3 in H4.
rewrite <- e in H4.   apply H4. inversion H5. auto. 
* inversion H5. 
destruct  (range_typ_dec r0 r1). 
exists ((a, (t, r0)) :: v4). 
 destruct (atom_eq_dec a a). Focus 2. exfalso;apply n2;auto. 
destruct (typ_eq_dec t t). Focus 2. exfalso;apply n2;auto. 
destruct (range_typ_dec r r0). exfalso;apply n1;auto. clear n2.  clear e4. clear e5. clear e3. clear Heqs. clear Heqs0.  clear e0.
clear e. rewrite e1 in n0. exfalso;apply n0;auto.  
exists ((a, (t, r0)) :: v4).       
destruct (atom_eq_dec a a). Focus 2. exfalso;apply n3;auto. clear e1. 
destruct (typ_eq_dec t t). Focus 2. exfalso;apply n3;auto. clear e1.      
remember (mergeDataStateFunc l x v4).  destruct e1.
destruct (range_typ_dec r r0). exfalso;apply n1;auto.   
destruct (range_typ_dec r r). Focus 2. exfalso;apply n4;auto. clear e1. 
exists ((a, (t, r0)) :: v5). split;auto. split;auto. inversion H6. f_equal. clear n3. clear n2. clear Heqs. clear Heqs0. clear Heqs1.
clear e0. clear e2.       

(*no error case *)
apply  IHl  with (x:=x) (v0:=v0) in Heqe1.  
destruct Heqe1. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe0. inversion Heqe0. 
rewrite H14 in Heqe2. destruct H13.  rewrite <- H8 in Heqe2.   inversion Heqe2. auto.      inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H.  apply H. apply H3.  
eapply noDataConf'. apply H. rewrite H1 in H.
 apply H. simpl. constructor. inversion H. assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.   inversion H0. apply H17.  
 inversion H2. apply H17. auto. inversion H5.  rewrite H16. auto. 
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0. apply H13.  
 inversion H2. apply H13. auto. inversion H5.  rewrite H7. auto. inversion H. auto. rewrite <- e3 in H4.
rewrite <- e in H4.   apply H4. rewrite H11. auto. 

(* error case *)
apply  IHl  with (x:=x) (v0:=v0) in Heqe1.  
destruct Heqe1. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe0.   inversion Heqe0. rewrite H13 in Heqe2.
destruct H12.  rewrite <- H8 in Heqe2. inversion Heqe2.         
 inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H.  apply H. apply H3.  
eapply noDataConf'. apply H. rewrite H1 in H.
 apply H. simpl. constructor. inversion H. assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0.  apply H16.  
 inversion H2. apply H16. auto. inversion H5.  rewrite H15. auto. 
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0. apply H12.  
 inversion H2. apply H12. auto. inversion H5.  rewrite H7. auto. inversion H. auto. rewrite <- e3 in H4.
rewrite <- e in H4.   apply H4. rewrite H11. auto.

*    apply  IHl  with (x:=x) (v0:=v0) in Heqe1.  
destruct Heqe1. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe0.   inversion Heqe0. 
 inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H.  apply H. apply H3.  
eapply noDataConf'. apply H. rewrite H1 in H.
 apply H. simpl. constructor. inversion H. assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0.  apply H12.  
 inversion H2. apply H12. auto. inversion H5.  rewrite H11. auto. 
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0. apply H8.  
 inversion H2. apply H8. auto. inversion H5.  rewrite H7. auto. inversion H. auto. rewrite <- e3 in H4.
rewrite <- e in H4.   apply H4. inversion H5. auto.

* destruct y. simpl in H6. inversion H6. destruct v1. simpl in H6. destruct p. destruct p. inversion H6.
destruct p. destruct p0. destruct p.   simpl in H6. simpl.   
destruct (atom_eq_dec a a2). Focus 2. destruct p0.   inversion H6.   destruct (atom_eq_dec a a3).
Focus 2. destruct p0.   inversion H6. destruct p0.   destruct (typ_eq_dec t t2). Focus 2. inversion H6. 
destruct  (typ_eq_dec t t3). Focus 2. inversion H6.  remember ( mergeDataStateFunc l y v1).
destruct e7. Focus 2. inversion H6.
destruct (range_typ_dec r2 r3).  

(**)
destruct ((atom_eq_dec a a1)). destruct ( typ_eq_dec t t1). 
remember  (mergeDataStateFunc l y v0). destruct e10. 
destruct (range_typ_dec r2 r1).               
exists (((a, (t, r2)) :: v4)). 
destruct (atom_eq_dec a a0). Focus 2. exfalso;apply n1;auto. destruct (atom_eq_dec a a).
Focus 2. exfalso;apply n1;auto. clear e12. destruct (typ_eq_dec t t0). Focus 2. exfalso;apply n1;auto.
destruct (typ_eq_dec t t). clear e13. Focus 2. exfalso;apply n1;auto. inversion H5. subst.  exfalso;apply n;auto.
destruct (range_typ_dec r2 r). inversion H5. subst. exfalso;apply n1;auto. rewrite H10 in n1. exfalso;apply n1;auto.
exfalso;apply n0;auto.       

exists (((a, (t, r2)) :: v4)).     
destruct (atom_eq_dec a a0). Focus 2. subst.    exfalso;apply n3;auto. destruct (atom_eq_dec a a).
Focus 2. exfalso;apply n3;auto. clear e11.   destruct (typ_eq_dec t t0). Focus 2. exfalso;apply n3;auto.
destruct (typ_eq_dec t t). clear e12. Focus 2. exfalso;apply n3;auto. 
remember (mergeDataStateFunc l x v4). destruct e12. 
destruct (range_typ_dec r0 r2). 
exists (((a, (t, r0)) :: v5)). split;auto. split;auto. inversion H6. rewrite e12. f_equal. subst. clear n1. clear n2.
clear e9.    

apply  IHl  with (x:=x) (v0:=v0) in Heqe7.  
destruct Heqe7. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe10. inversion Heqe10. 
rewrite H11 in Heqe12.  rewrite <- H8 in Heqe12.   inversion Heqe12. auto.      inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H. rewrite <- e0 in H. rewrite <- e2 in H.    apply H.  rewrite <- e2 in H3. rewrite <- e0 in H3.  apply H3.
  eapply noDataConf'. apply H. rewrite H1 in H. rewrite e3. rewrite e5. apply H. simpl.

simpl. constructor. inversion H. assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'. inversion H0.  apply H12.  
 inversion H2. apply H13. auto. inversion H5.  rewrite H11. auto. 
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'. inversion H0. apply H8.  
 inversion H2. apply H9. auto. inversion H5.  rewrite H7. auto. inversion H. auto.
 rewrite <- e3 in H4. rewrite <- e5 in H4. rewrite<- e4 in H4. rewrite <- e6 in H4. apply H4.
inversion H5. auto.     

destruct (range_typ_dec r0 r). exfalso;apply n0;auto. clear n4. exists ((a, (t, r0)) :: v5).
split;auto. split;auto. inversion H6.  inversion H5. subst. exfalso;apply n3;auto.      

apply  IHl  with (x:=x) (v0:=v0) in Heqe7.  
destruct Heqe7. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe10. inversion Heqe10.  
rewrite H11 in Heqe12.  rewrite <- H8 in Heqe12.   inversion Heqe12. auto.      inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. rewrite <- e1 in H. 
rewrite <- e in H.   apply H. 
simpl. constructor. inversion H. assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0.  apply H13.  
 inversion H2. apply H13. auto. inversion H5. inversion H2.   auto.
inversion H2. inversion H. auto. rewrite H8 in H12. auto.      
rewrite <- e in H3. 
rewrite <- e1 in H3. rewrite <- e0 in H3. rewrite <- e2 in H3. apply H3.     
eapply noDataConf'. apply H. rewrite H1 in H. rewrite e3. rewrite e5. apply H.
simpl. constructor. 
 assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'. inversion H0.  apply H9.  
 inversion H2. apply H9. auto. inversion H5. inversion H2.  rewrite H7. inversion H;auto.
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'. inversion H0.  apply H9.  
 inversion H2. apply H9. auto. inversion H5. inversion H2.  rewrite H7. inversion H;auto. rewrite <- H13. auto.    
rewrite <- e3 in H4. rewrite <- e5 in H4. rewrite <- e4 in H4. rewrite <- e6 in H4. apply H4. inversion H5. auto.       
  

apply  IHl  with (x:=x) (v0:=v0) in Heqe7.  
destruct Heqe7. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe10. inversion Heqe10.    inversion H;auto.
 inversion H0. auto. inversion H1. auto. inversion H2. auto.      
eapply noDataConf'.
apply H. rewrite H0 in H. rewrite<- e1 in H. rewrite <- e in H.   apply H.
rewrite H2 in H. rewrite e0. rewrite e2. apply H. rewrite <- e in H3. rewrite <- e0 in H3.  
rewrite <- e1 in H3. apply H3.          
eapply noDataConf'. apply H.  rewrite H1 in H.  rewrite e3. rewrite e5. apply H.
simpl. constructor. 
 assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'. inversion H0.  apply H9.  
 inversion H2. apply H9. auto. inversion H5. rewrite H7. inversion H;auto.
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'. inversion H0.  apply H9.  
 inversion H2. apply H9. auto. inversion H5. rewrite H7. inversion H;auto. 
rewrite <- e3 in H4. rewrite <- e5 in H4. rewrite <- e4 in H4. rewrite <- e6 in H4. apply H4. inversion H5. auto.
exfalso;apply n1;auto.
exfalso;apply n1;auto.

destruct (range_typ_dec r2 r).
destruct (atom_eq_dec a a1). Focus 2. exfalso;apply n2;auto.
destruct (typ_eq_dec t t1). Focus 2. exfalso;apply n2;auto.     
remember (mergeDataStateFunc l y v0 ).
destruct e10.  Focus 2.


 apply  IHl  with (x:=x) (v0:=v0) in Heqe7.  
destruct Heqe7. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe10. inversion Heqe10.    inversion H;auto.
 inversion H0. auto. inversion H1. auto. inversion H2. auto.      
eapply noDataConf'.
apply H. rewrite H0 in H. rewrite<- e1 in H. rewrite <- e in H.   apply H.
simpl. constructor. 
 assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'. inversion H0.  apply H9.  
 inversion H2. apply H9. auto. inversion H2. inversion H;auto.
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'. inversion H0.  apply H9.  
 inversion H2. apply H9. auto. inversion H2. inversion H;auto. rewrite <- H9. auto.  
rewrite <- e3 in H4. rewrite <- e5 in H4. rewrite <- e4 in H4. rewrite <- e6 in H4.
rewrite <- e in H3. rewrite <- e1 in H3. rewrite <- e0 in H3. rewrite <- e2 in H3. apply H3.
eapply noDataConf'. apply H.  rewrite H1 in H.  rewrite e3. rewrite e5. apply H.
simpl. constructor. 
 assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'. inversion H0.  apply H9.  
 inversion H2. apply H9. auto. inversion H5. rewrite H7. inversion H;auto.
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'. inversion H0.  apply H9.  
 inversion H2. apply H9. auto. inversion H5. rewrite H7. inversion H;auto. 
rewrite <- e3 in H4. rewrite <- e5 in H4. rewrite <- e4 in H4. rewrite <- e6 in H4. apply H4. inversion H5. auto.


destruct  (range_typ_dec r2 r1 ). exists (((a, (t, r2)) :: v4)). 
destruct (atom_eq_dec a a0). Focus 2. exfalso;apply n2;auto.      
destruct (atom_eq_dec a a). Focus 2. exfalso;apply n2;auto. clear e12. 
 destruct (typ_eq_dec t t0). Focus 2. exfalso;apply n2;auto. 
destruct  (typ_eq_dec t t). Focus 2. exfalso;apply n2;auto. clear e13. 

remember (mergeDataStateFunc l x v4). 
destruct e13. subst.
destruct (range_typ_dec r0 r). subst. exfalso;apply n;auto. 
exists ((a0, (t0, r0)) :: v5). split;auto. split;auto. inversion H6. inversion H5. subst. subst.   
f_equal. 

(*no error case *)
apply  IHl  with (x:=x) (v0:=v0) in Heqe7.  
destruct Heqe7. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe10. inversion Heqe10.  
rewrite H13 in Heqe13.  rewrite <- H8 in Heqe13.   inversion Heqe13. auto.      inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. Focus 2.  apply H3.
  simpl. constructor. inversion H. inversion H2. auto.
inversion H. inversion H2. auto.    
eapply noDataConf'. apply H. rewrite H1 in H.
 apply H. simpl. constructor. inversion H. assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'. inversion H0. apply H14.  
 inversion H2. apply H14. auto. inversion H5.  rewrite H13. auto. 
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0. apply H8.  
 inversion H2. apply H8. auto. inversion H5.  rewrite H7. auto. inversion H. auto. apply H4.
 auto.

subst. 

apply  IHl  with (x:=x) (v0:=v0) in Heqe7.  
destruct Heqe7. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe10.   inversion Heqe10. rewrite H11 in Heqe13.
 rewrite <- H8 in Heqe13. inversion Heqe13.         
 inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. Focus 2. rewrite <- e0 in H3. rewrite <- e9 in H3.    apply H3.
Focus 2.   
eapply noDataConf'. apply H. rewrite H1 in H. rewrite e3. rewrite e5. apply H. Focus 2. 
rewrite <- e3 in H4. rewrite <- e4 in H4. rewrite <- e5 in H4. rewrite <- e6 in H4. apply H4.         
simpl. constructor. inversion H. assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0.  apply H12.  
 inversion H2. apply H13. auto. inversion H5.  rewrite H11. auto. 
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.   inversion H0. apply H8.  
 inversion H2. apply H9. auto. inversion H5.  rewrite H7. auto. inversion H. auto. 
simpl. constructor. inversion H2. inversion H. auto. inversion H2. inversion H. rewrite <- H8. auto.
inversion H5. auto.           

exists ((a, (t, r1)) :: v4). subst.   
destruct (atom_eq_dec a0 a0). Focus 2. exfalso;apply n3;auto. 
destruct (typ_eq_dec t0 t0). Focus 2. exfalso;apply n3;auto.
remember (mergeDataStateFunc l x v4).
destruct e7. destruct (range_typ_dec r0 r1). exfalso;apply n;auto. 
clear n3. destruct (range_typ_dec r0 r ). exfalso;apply n0;auto. clear n3. 
exists ((a0, (t0, r0)) :: v5). split;auto. split;auto. inversion H6. inversion H5. 
apply f_equal. subst.  

apply  IHl  with (x:=x) (v0:=v0) in Heqe7.  
destruct Heqe7. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe10. inversion Heqe10.  
rewrite H13 in Heqe0.  rewrite <- H8 in Heqe0.   inversion Heqe0. auto.      inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. Focus 2.  apply H3.
  simpl. constructor. inversion H. inversion H2. auto.
inversion H. inversion H2. auto.    
eapply noDataConf'. apply H. rewrite H1 in H. rewrite e3. rewrite e5.  
 apply H. simpl. constructor. inversion H. assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'. inversion H0. apply H14.  
 inversion H2. apply H14. auto. inversion H5.  rewrite H13. auto. 
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'. inversion H0. apply H8.  
 inversion H2. apply H8. auto. inversion H5.  rewrite H7. auto. inversion H. auto. rewrite <- e3 in H4.
rewrite <- e5 in H4.    apply H4. 
 auto.

(* error case *)
apply  IHl  with (x:=x) (v0:=v0) in Heqe7.  
destruct Heqe7. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe10.   inversion Heqe10. rewrite H11 in Heqe0.
 rewrite <- H8 in Heqe0. inversion Heqe0.         
 inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H.  rewrite e0. rewrite e9.    apply H. rewrite <- e9 in H3. rewrite <- e0 in H3.   apply H3.  
eapply noDataConf'. apply H. rewrite H1 in H. rewrite e3. rewrite e5. apply H.    
 simpl. constructor. inversion H. assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'. inversion H0.  apply H12.  
 inversion H2. apply H13. auto. inversion H5.  rewrite H11. auto. 
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0. apply H8.  
 inversion H2. apply H9. auto. inversion H5.  rewrite H7. auto. inversion H.  auto. rewrite <- e3 in H4.
rewrite <- e5 in H4. rewrite <- e4 in H4. rewrite <- e6 in H4.     apply H4. inversion H5. auto.   

destruct (atom_eq_dec a a1). Focus 2. exfalso;apply n3;auto. 
destruct (typ_eq_dec t t1). Focus 2. exfalso;apply n3;auto. 
remember (mergeDataStateFunc l y v0). destruct e9.
Focus 2.

apply  IHl  with (x:=x) (v0:=v0) in Heqe7.  
destruct Heqe7. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe9.   inversion Heqe9.     
 inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. rewrite e. rewrite e1.   apply H.
Focus 2.   rewrite <- e in H3. rewrite <- e1 in H3. rewrite <- e0 in H3. rewrite <- e2 in H3.     apply H3.  
 simpl. constructor. inversion H. inversion H2. auto. inversion H2. inversion H. rewrite <- H8. auto.     
 eapply noDataConf'.
apply H. rewrite H1 in H. rewrite e3. rewrite e5.   apply H.
Focus 2.   rewrite <- e3 in H4. rewrite <- e5 in H4. rewrite <- e4 in H4. rewrite <- e6 in H4.     apply H4.  
 simpl. constructor. assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0. apply H9.  
 inversion H2. apply H9. auto. inversion H5.  rewrite H7.  inversion H.  auto.
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'. inversion H0. apply H9.  
 inversion H2. apply H9. auto. inversion H5.  rewrite H7.  inversion H.  auto.
 inversion H5;auto.

destruct (atom_eq_dec a a0). Focus 2. exfalso;apply n3;auto.       
destruct (range_typ_dec r2 r1).  exists ((a, (t, r2)) :: v4).
destruct (atom_eq_dec a a). Focus 2. exfalso;apply n3;auto. 
destruct (typ_eq_dec t t0). Focus 2. exfalso;apply n3;auto.
destruct (typ_eq_dec t t). Focus 2. exfalso;apply n3;auto.
clear e11. clear e13.   
remember (mergeDataStateFunc l x v4).
destruct e11. 
Focus 2.

apply  IHl  with (x:=x) (v0:=v0) in Heqe7.  
destruct Heqe7. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe9.   inversion Heqe9. rewrite H11 in Heqe11.
rewrite <- H8 in Heqe11. inversion Heqe11.        
 inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. rewrite e. rewrite e1.   apply H.
Focus 2.   rewrite <- e in H3. rewrite <- e1 in H3. rewrite <- e0 in H3. rewrite <- e2 in H3.     apply H3.  
 simpl. constructor. inversion H. inversion H2. auto. inversion H2. inversion H. rewrite <- H8. auto.     
 eapply noDataConf'.
apply H. rewrite H1 in H. rewrite e3. rewrite e5.   apply H.
Focus 2.   rewrite <- e3 in H4. rewrite <- e5 in H4. rewrite <- e4 in H4. rewrite <- e6 in H4.     apply H4.  
 simpl. constructor. assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'. inversion H0. apply H9.  
 inversion H2. apply H9. auto. inversion H5.  rewrite H7.  inversion H.  auto.
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0. apply H9.  
 inversion H2. apply H9. auto. inversion H5.  rewrite H7.  inversion H.  auto.
 inversion H5;auto.          

destruct (range_typ_dec r0 r2). subst.  exists ((a0, (t0, r1)) :: v5). split;auto.
split;auto.  inversion H6. f_equal.

apply  IHl  with (x:=x) (v0:=v0) in Heqe7.  
destruct Heqe7. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe9. inversion Heqe9.  
rewrite H10 in Heqe11. destruct H9.    rewrite <- H8 in Heqe11.   inversion Heqe11. auto.      inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H. rewrite e0. rewrite e8. apply H. rewrite <- e0 in H3.
rewrite <- e8 in H3.  apply H3.
eapply noDataConf'. apply H. rewrite H1 in H. rewrite e3. rewrite e5. apply H.     
 simpl. constructor. inversion H. assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0. apply H13.  
 inversion H2. apply H14. auto. inversion H5.  rewrite H12. auto. 
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0. apply H9.  
 inversion H2. apply H10. auto. inversion H5.  rewrite H7. auto. rewrite <- e3 in H4. rewrite <- e4 in H4.
rewrite <- e5 in H4. rewrite <- e6 in H4. apply H4. inversion H5;auto. 
    
destruct (range_typ_dec r0 r ). exfalso;apply n0;auto.  clear n4. 
exists ((a, (t, r0)) :: v5). split;auto. split;auto. inversion H6.  subst.        
inversion H5. subst. 

unfold noDataConflict in H4. rewrite e3 in H4.  rewrite e5 in H4. destruct H4 with a2.
assert (getValue a2 ((a2, (t2, r1)) :: y) = getValue a2 ((a2, (t2, r0)) :: v)).
apply H10. split. unfold not. intros.  simpl in H11. destruct a2;inversion H7.  inversion H12. inversion H12. 
destruct (atom_eq_dec (AIdent s) (AIdent s)). inversion H11. exfalso;apply n2;auto. exfalso;apply n4;auto. inversion H12. 
inversion H12. inversion H12. unfold not. intros. simpl in H11.

destruct a2;inversion H7. inversion H12. inversion H12. 
destruct (atom_eq_dec (AIdent s) (AIdent s)). inversion H11.  exfalso;apply n0;auto. exfalso;apply n4;auto. inversion H12. 
inversion H12. inversion H12.  simpl in H11. destruct a2;inversion H7. inversion H12. inversion H12. 
destruct (atom_eq_dec (AIdent s) (AIdent s)). inversion H11. exfalso;apply n1;auto. exfalso;apply n4;auto. inversion H12. 
inversion H12. inversion H12.

exists  ((a, (t, r2)) :: v4). destruct (atom_eq_dec a a). Focus 2.  exfalso;apply n4;auto.
clear e10. destruct (typ_eq_dec t t0). Focus 2 . exfalso;apply n4;auto.
destruct (typ_eq_dec t t). Focus 2. exfalso;apply n4;auto. clear e11. 
remember (mergeDataStateFunc l x v4).
destruct e11. Focus 2.

subst. apply  IHl  with (x:=x) (v0:=v0) in Heqe7.  
destruct Heqe7. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe9.    inversion Heqe9.   rewrite H11 in Heqe11.
 rewrite <- H8 in Heqe11. inversion Heqe11.         
 inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H. rewrite e0. rewrite e8.   
apply H. rewrite <- e0 in H3. rewrite <- e8 in H3. apply H3.  
eapply noDataConf'. apply H. rewrite H1 in H. rewrite e3. rewrite e5. apply H.    
 simpl. constructor. inversion H. assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0.  apply H12.  
 inversion H2. apply H13. auto. inversion H5.  rewrite H11. auto. 
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0. apply H8.  
 inversion H2. apply H9. auto. inversion H5.  rewrite H7. auto. inversion H.  auto. rewrite <- e3 in H4.
rewrite <- e5 in H4. rewrite <- e4 in H4. rewrite <- e6 in H4.     apply H4. inversion H5. auto.

   
destruct (range_typ_dec r0 r2). subst.  
exists (((a0, (t0, r2)) :: v5)). split;auto. split;auto. inversion H6. f_equal.

apply  IHl  with (x:=x) (v0:=v0) in Heqe7. subst.    
destruct Heqe7. destruct H7. destruct H7. destruct H8.  rewrite <- H7 in Heqe9. inversion Heqe9.  
rewrite H11 in Heqe11.  rewrite <- H8 in Heqe11.   inversion Heqe11. auto.      inversion H;auto. inversion H0.
auto. inversion H1. auto. inversion H2. auto.   
SearchAbout noDataConflict.   eapply noDataConf'.
apply H. rewrite H0 in H. apply H. rewrite H2 in H. rewrite e0. rewrite e8. apply H.
rewrite <- e0 in H3. rewrite <- e8 in H3.   apply H3.
eapply noDataConf'. apply H. rewrite H1 in H. rewrite e3. rewrite e5. apply H.    
simpl. constructor. inversion H. assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0. apply H13.  
 inversion H2. apply H14. auto. inversion H5.  rewrite H12. auto. 
assert (dom v = dom l). 
eapply mergeDataStateUniqInvariant'.  inversion H0. apply H9.  
 inversion H2. apply H10. auto. inversion H5.  rewrite H7. auto. rewrite <- e3 in H4.
rewrite <- e5 in H4. rewrite <- e4 in H4. rewrite <- e6 in H4.    apply H4.
inversion H5. auto.  

destruct (range_typ_dec r0 r). exfalso;apply n0;auto. 
subst. 
exists (((a0, (t0, r0)) :: v5)). split;auto. split;auto.
inversion H6.  subst. clear Heqs.   clear e9.  clear Heqs0. clear Heqs1.
    clear e10. clear e8. clear e7. clear n5.     
inversion H5. subst. 
        
unfold noDataConflict in H4.  destruct H4 with a2.
assert (getValue a2 ((a2, (t2, r2)) :: y) = getValue a2 ((a2, (t2, r0)) :: v)).
apply H10. split. unfold not. intros.  simpl in H11. destruct a2;inversion H7.  inversion H12. inversion H12. 
destruct (atom_eq_dec (AIdent s) (AIdent s)). inversion H11. exfalso;apply n2;auto. exfalso;apply n5;auto. inversion H12. 
inversion H12. inversion H12. unfold not. intros. simpl in H11.

destruct a2;inversion H7. inversion H12. inversion H12. 
destruct (atom_eq_dec (AIdent s) (AIdent s)). inversion H11.  exfalso;apply n0;auto. exfalso;apply n5;auto. inversion H12. 
inversion H12. inversion H12.  simpl in H11. destruct a2;inversion H7. inversion H12. inversion H12. 
destruct (atom_eq_dec (AIdent s) (AIdent s)). inversion H11. exfalso;apply n1;auto. exfalso;apply n5;auto. inversion H12. 
inversion H12. inversion H12.
Qed.  



Lemma mergeControlStateFuncEquivOnCom': forall (cso  x y v0 v1 v2: scenario_env), 
uniqList (dom (cso)) ->
(dom (cso) = dom(x)) ->
(dom (cso) = dom (y)) ->
(dom (cso) = dom (v0)) ->
noControlConflict cso x v0 ->
noControlConflict cso y v1 ->
Result v1 = mergeControlStateFunc cso x v0 ->
Result v2 = mergeControlStateFunc cso y v1 ->
(exists v1' v2',
Result v1' = mergeControlStateFunc cso y v0 /\
Result v2' = mergeControlStateFunc cso x v1' /\
 v2 = v2').
Proof.
Admitted. (*similar to the proof of data state*)
                     

Lemma filterListInvariant: forall (A:Type) l a0 lst  decA,
uniqList (a0::lst) ->
~In a0 l ->
@filterList A (a0 :: lst) l decA = @filterList A lst l decA.
Proof. intros A l.
induction l;intros;simpl;auto.
destruct (decA a a0).
remember (inList decA a lst).
destruct (b).
apply IHl. auto. unfold not. intros. unfold not in H0. apply H0. right;auto.
rewrite e in H0. exfalso;apply H0. left;auto.
remember (inList decA a lst).  destruct b.
apply IHl; auto; unfold not;  intros. apply H0; right;auto.
f_equal. apply IHl;auto; unfold not;  intros. apply H0; right;auto.
Qed. 

Lemma filterListInvariant': forall (A:Type) lst' l a0 lst  decA,
uniqList (a0::lst) ->
uniqList  (lst' ++ a0::l) ->
@filterList A (a0 :: lst) (lst' ++ a0::l) decA = @filterList A lst (lst'++l) decA.
Proof. intros A lst'.
induction lst';intros;simpl;auto.
- simpl in H0. destruct (decA a0 a0). Focus 2. exfalso;apply n;auto.
inversion H0. subst. inversion H;subst.
apply filterListInvariant;auto.
-  destruct (decA a a0).    
remember (inList decA a lst).
destruct b. simpl. apply IHlst';auto. inversion H0. subst.
auto. 
inversion H0;subst. exfalso;apply H4;auto.
apply in_or_app. right;left;auto.  
simpl.           
remember (inList decA a lst).
destruct b.
 apply IHlst';auto. inversion H0;auto.
f_equal. apply IHlst';auto. inversion H0;auto.        

Qed. 

Lemma filterListMiddle: forall (A:Type) (lst' lst  l:list A) (a0:A) decA,
uniqList (lst) ->
uniqList (lst'++a0::l) ->
In a0 lst ->
filterList (lst) (lst' ++ a0::l) decA = filterList (lst) (lst' ++ l) decA.
Proof.   intros A lst'. induction lst'.
- intros. simpl. simpl in H0. 
remember (inList decA a0 lst ).
destruct b. auto. SearchAbout inList.
symmetry in Heqb.  apply reverseinListFalse in Heqb. exfalso;apply Heqb;auto.
- intros. simpl.   
remember (inList decA a lst).
destruct b.
apply IHlst';auto. inversion H0;auto.
f_equal. apply IHlst';auto. inversion H0;auto.          
Qed. 

Lemma filterListIn: forall (A:Type) lst lst' l  a decA,
uniqList lst ->
uniqList lst' ->
In a lst ->
uniqList (lst'++a::l) ->
@filterList A lst (lst' ++ l) decA = @filterList A lst (lst' ++ a::l) decA.
Proof. intros A lst.
induction lst.
- intros. inversion H1.
- intros. destruct H1.
+ inversion H;subst.
SearchAbout filterList. 
SearchAbout filterList. 
assert (a0::lst = (app (a0::nil) lst)).
simpl. auto. rewrite H1.
rewrite filterNoEffect. simpl.  Focus 2. simpl. auto. Focus 2.
 rewrite uniqListNoDupEq.
eapply NoDup_remove_1.  
rewrite <- uniqListNoDupEq. 
apply H2.  SearchAbout filterList. simpl. rewrite  filterListInvariant' with (a0:=a0);auto.
intros. destruct H3. rewrite <- H3.
rewrite  uniqListNoDupEq in H2. apply NoDup_remove_2 in H2.
auto.   
  inversion H3.
+ simpl. assert (a=a0\/a<>a0).
apply excluded_middle. 
destruct H3. 
rewrite H3.      
rewrite filterListInvariant';auto. Focus 2. rewrite <- H3. auto. 
rewrite filterListInvariant;auto. rewrite <- H3;auto.     rewrite  uniqListNoDupEq in H2.
apply NoDup_remove_2 in H2.
auto.
assert (In a (lst'++l) \/ ~ In a (lst'++l)).
apply excluded_middle.
destruct H4.
Focus 2. rewrite  filterListInvariant with (a0:=a);auto.
rewrite  filterListInvariant with (a0:=a);auto.
apply IHlst. inversion H;auto. auto. auto. auto. 
unfold not. intros. apply H4.      
apply in_app_or in H5. destruct H5.
apply in_or_app. left;auto.
destruct H5. exfalso;apply H3;auto.
apply in_or_app. right;auto.        
  rewrite filterListMiddle;auto. right;auto.
Qed.       

Lemma filterListMiddle_2: forall(A:Type)   lst' l lst x decA,
uniqList lst ->
uniqList lst' ->
uniqList l ->
~(In x lst) ->
~(In x lst') ->
~(In x l) ->
equivList (filterList lst' (lst ++ x::l) decA)  (x::(@filterList A lst' (lst++ l) decA)).
Proof. intros A lst'.
induction lst;intros;simpl. 
- remember (inList decA x lst' ). destruct b. simpl. SearchAbout inList. 
symmetry in Heqb. apply reverseinListLemma in Heqb. 
exfalso;apply H3;auto. apply Permutation_refl. 
- remember (inList decA a lst' ).
destruct b.
apply IHlst;auto. inversion H;auto. unfold not.  intros.
unfold not in H2. apply H2. right;auto.
assert (Permutation (x::a::filterList lst' (lst ++ l) decA) (a::x::filterList lst' (lst ++ l) decA)).
apply perm_swap.
apply Permutation_sym.
eapply perm_trans. apply H5. apply perm_skip.
apply Permutation_sym. apply IHlst;auto.
inversion H ;auto. unfold not .
 intros. apply H2. right;auto.
Qed.      

Lemma mergeListEquivOnCom': forall (A:Type) lst1 lst lst' lst0 lst0'  decA, 
uniqList lst ->
uniqList lst' ->
uniqList lst0 ->
uniqList lst0' ->
uniqList lst1 ->
equivList lst lst0 ->
equivList lst' lst0' ->
equivList  (@mergeList' A lst' (@mergeList' A lst lst1 decA) decA) (@mergeList' A lst0 (@mergeList' A lst0' lst1 decA) decA ).
Proof. intros A lst1.
induction lst1;intros;simpl.
- unfold mergeList'. simpl. rewrite app_nil_r. rewrite app_nil_r.
SearchAbout mergeList'. apply mergeListEquiv';auto. apply Permutation_sym;auto.


-   unfold mergeList'. simpl.
 remember (inList decA a lst).
remember (inList decA a lst0'). 
destruct b.
destruct b0.
unfold mergeList' in IHlst1. apply IHlst1;auto. inversion H3;auto. 
rewrite <- filterListIn with (a:=a);auto. apply IHlst1;auto. inversion H3;auto. eapply Permutation_in.
apply H4. SearchAbout inList. eapply reverseinListLemma. symmetry. apply Heqb.
rewrite uniqListNoDupEq.
assert (NoDup (a::(app lst0' (filterList lst0' lst1 decA)))).
constructor.
inversion H3;subst.
unfold not.  intros. apply in_app_or in H6. destruct H6. SearchAbout inList. symmetry in Heqb0.
apply reverseinListFalse in Heqb0. exfalso;apply Heqb0;auto. 
apply filterL2 in H6. exfalso;apply H9;auto. SearchAbout mergeList'.  
rewrite <- uniqListNoDupEq. 
apply uniqMerge;auto. inversion H3;auto. 
eapply Permutation_NoDup. Focus 2. apply H6. apply Permutation_middle.
destruct b0. rewrite <- filterListIn with (a:=a). 
apply IHlst1;auto. inversion H3;auto. auto. auto. 
eapply Permutation_in. apply Permutation_sym. apply H5.          
 symmetry in Heqb0.            
eapply reverseinListLemma. apply Heqb0. 
rewrite uniqListNoDupEq.
assert (NoDup (a::(app lst (filterList lst lst1 decA)))).
constructor.  unfold not. intros.
apply in_app_or in H6.
destruct H6. symmetry in Heqb. SearchAbout inList.    
apply reverseinListFalse in Heqb. exfalso;apply Heqb;auto.
apply filterL2 in H6. inversion H3;subst. exfalso;apply H10;auto.
rewrite <- uniqListNoDupEq.      
apply uniqMerge;auto.  inversion H3;auto.
eapply Permutation_NoDup. Focus 2. apply H6.
apply Permutation_middle.
assert (Permutation  (a::(lst' ++ filterList lst' (lst ++ filterList lst lst1 decA) decA))  (lst' ++ a :: filterList lst' (lst ++ filterList lst lst1 decA) decA)).
apply Permutation_middle.
assert (Permutation  (a::(lst0 ++ filterList lst0 (lst0' ++ filterList lst0' lst1 decA) decA)) 
 (lst0 ++ a :: filterList lst0 (lst0' ++ filterList lst0' lst1 decA) decA)).
apply Permutation_middle.
assert (Permutation (a :: lst' ++ filterList lst' (lst ++ filterList lst lst1 decA) decA) (a :: lst0 ++ filterList lst0 (lst0' ++ filterList lst0' lst1 decA) decA)).
apply perm_skip. apply IHlst1;auto. inversion H3;auto. 
assert (Permutation (lst' ++ a :: filterList lst' (lst ++ filterList lst lst1 decA) decA)  (lst' ++ filterList lst' (lst ++ a :: filterList lst lst1 decA) decA)).
apply Permutation_app_head.
 apply Permutation_sym. apply filterListMiddle_2;auto. SearchAbout filterList.           
apply uniqListFilter;auto.  inversion H3;auto.     symmetry in Heqb. symmetry in Heqb0.
apply reverseinListFalse in Heqb. auto.
symmetry in Heqb0. apply reverseinListFalse in Heqb0. unfold not.  intros. apply Heqb0.
eapply Permutation_in. apply H5. auto. SearchAbout filterList.  unfold not. intros. 
 eapply filterL2 in H9. inversion H3;subst.  exfalso;apply H13;auto. 
assert (Permutation (lst0 ++ a :: filterList lst0 (lst0' ++ filterList lst0' lst1 decA) decA) 
 (lst0 ++ filterList lst0 (lst0' ++ a :: filterList lst0' lst1 decA) decA)).
apply Permutation_app_head.
 apply Permutation_sym. apply filterListMiddle_2;auto. SearchAbout filterList.           
apply uniqListFilter;auto. inversion H3;auto.  symmetry in Heqb. symmetry in Heqb0.
apply reverseinListFalse in Heqb0. auto.  
symmetry in Heqb. apply reverseinListFalse in Heqb. unfold not.  intros. apply Heqb.
eapply Permutation_in. apply Permutation_sym.  apply H4. auto. SearchAbout filterList.  unfold not. intros. 
 eapply filterL2 in H10.  inversion H3;subst.  exfalso;apply H14;auto. 
eapply Permutation_sym in H9.
eapply perm_trans. apply H9.
apply Permutation_sym in H6. eapply perm_trans.
apply H6.
eapply perm_trans. apply H8. eapply perm_trans. apply H7.
auto.         
Qed. 

Lemma mergeListEquivOnCom'': forall (A:Type) lst1 lst1' lst lst' lst0 lst0'  decA, 
uniqList lst ->
uniqList lst' ->
uniqList lst0 ->
uniqList lst0' ->
uniqList lst1 ->
uniqList lst1' ->
equivList lst lst0 ->
equivList lst' lst0' ->
equivList lst1 lst1' ->
equivList  (@mergeList' A lst' (@mergeList' A lst lst1 decA) decA) (@mergeList' A lst0 (@mergeList' A lst0' lst1' decA) decA ).
Proof. intros. generalize dependent lst.  generalize dependent lst'.  generalize dependent lst0. generalize dependent lst0'.  

induction H7.   
- intros.  unfold mergeList'.  rewrite app_nil_r. rewrite app_nil_r. 
SearchAbout mergeList'.
apply mergeListEquiv';auto. apply Permutation_sym. auto.  
- intros.  inversion H3;subst.  inversion H4;subst. 
unfold mergeList'.  
unfold mergeList' in IHPermutation. 
simpl.      
remember (inList decA x lst).
destruct b. 
remember (inList decA x lst0' ).
destruct b.  
(*remember H0. clear Hequ.   
apply IHlst1 with (lst:=lst) (decA:=decA) in H0. Focus 2. auto. Focus 2. auto.*)
+ apply IHPermutation; auto.  
+ SearchAbout filterList.   SearchAbout equivList. Print filterListIn.  
rewrite <- filterListIn;auto. SearchAbout inList. eapply Permutation_in. apply H5.      eapply reverseinListLemma. symmetry. apply Heqb.
assert (uniqList (x::(app lst0' (filterList lst0' l'0 decA)))).
Print uniqList.
apply uniqL_push. SearchAbout mergeList'.   
apply uniqMerge;auto. 
unfold not. intros. apply in_app_or in H8.
destruct H8. 
symmetry in Heqb0.      
eapply reverseinListFalse in  Heqb0.
exfalso;apply Heqb0;auto.
unfold not in H13. apply H13.
eapply filterL2. apply H8. 
 rewrite  uniqListNoDupEq in H8.
rewrite  uniqListNoDupEq.
eapply Permutation_NoDup. Focus 2.
apply H8.
apply Permutation_middle.     

+ remember (inList decA x lst0').
destruct b.  
rewrite <- filterListIn. apply IHPermutation;auto. auto. auto. eapply Permutation_in.
apply Permutation_sym. apply H6. SearchAbout inList.  eapply reverseinListLemma.
symmetry. apply Heqb0.
assert (uniqList (x::(app lst (filterList lst l decA)))).
constructor. SearchAbout mergeList'.  apply uniqMerge;auto. 
unfold not.  intros. apply  in_app_or in H8. destruct H8. SearchAbout inList. symmetry in Heqb.
SearchAbout inList. apply reverseinListFalse in Heqb. exfalso;apply Heqb;auto.
apply filterL2 in H8. exfalso;apply H11;auto. 
rewrite  uniqListNoDupEq in H8.
rewrite  uniqListNoDupEq.
eapply Permutation_NoDup. Focus 2. apply H8. apply Permutation_middle.
 SearchAbout filterList.            
assert (Permutation  (x::(lst' ++ filterList lst' (lst ++ filterList lst l decA) decA))  (lst' ++ x :: filterList lst' (lst ++ filterList lst l decA) decA)).
apply Permutation_middle.
assert (Permutation  (x::(lst0 ++ filterList lst0 (lst0' ++ filterList lst0' l'0 decA) decA)) 
 (lst0 ++ x :: filterList lst0 (lst0' ++ filterList lst0' l'0 decA) decA)).
apply Permutation_middle.
assert (Permutation (x :: lst' ++ filterList lst' (lst ++ filterList lst l decA) decA) (x :: lst0 ++ filterList lst0 (lst0' ++ filterList lst0' l'0 decA) decA)).
apply perm_skip. apply IHPermutation;auto.
assert (Permutation (lst' ++ x :: filterList lst' (lst ++ filterList lst l decA) decA)  (lst' ++ filterList lst' (lst ++ x :: filterList lst l decA) decA)).
apply Permutation_app_head.
 apply Permutation_sym. apply filterListMiddle_2;auto. SearchAbout filterList.           
apply uniqListFilter;auto. symmetry in Heqb. symmetry in Heqb0.
apply reverseinListFalse in Heqb. auto.  
symmetry in Heqb0. apply reverseinListFalse in Heqb0. unfold not.  intros. apply Heqb0.
eapply Permutation_in. apply H6. auto. SearchAbout filterList.  unfold not. intros. 
 eapply filterL2 in H15. exfalso;apply H11;auto. 
assert (Permutation (lst0 ++ x :: filterList lst0 (lst0' ++ filterList lst0' l'0 decA) decA) 
 (lst0 ++ filterList lst0 (lst0' ++ x :: filterList lst0' l'0 decA) decA)).
apply Permutation_app_head.
 apply Permutation_sym. apply filterListMiddle_2;auto. SearchAbout filterList.           
apply uniqListFilter;auto. symmetry in Heqb. symmetry in Heqb0.
apply reverseinListFalse in Heqb0. auto.  
symmetry in Heqb. apply reverseinListFalse in Heqb. unfold not.  intros. apply Heqb.
eapply Permutation_in. apply Permutation_sym. apply H5. auto. SearchAbout filterList.  unfold not. intros. 
 eapply filterL2 in H16. exfalso;apply H13;auto. 
eapply Permutation_sym in H15.
eapply perm_trans. apply H15.
apply Permutation_sym in H8. eapply perm_trans.

apply H8. eapply perm_trans.
apply H14. eapply perm_trans.
apply H9. apply H16.         
- intros. unfold mergeList'.
SearchAbout filterList. SearchAbout filterList.    
assert (Permutation (lst' ++ filterList lst' (lst ++ filterList lst (y :: x :: l) decA) decA) 
(lst0 ++ filterList lst0 (lst0' ++ filterList lst0' (y :: x :: l) decA) decA)).
apply  mergeListEquivOnCom';auto . 
eapply perm_trans.  apply H7.
apply Permutation_app_head.
SearchAbout mergeList'.  
assert (Permutation (lst0' ++ filterList lst0' (y :: x :: l) decA)   (lst0' ++ filterList lst0' (x :: y :: l) decA)).
apply mergeListEquiv;auto. apply Permutation_refl. apply perm_swap. 
SearchAbout filterList.     
eapply filterListEquiv'. apply Permutation_refl.
apply H8.   

-intros. 
assert (equivList (mergeList' lst' (mergeList' lst l decA) decA)
                   (mergeList' lst0 (mergeList' lst0' l'0 decA) decA)).
apply IHPermutation1;auto. 
rewrite  uniqListNoDupEq.
eapply Permutation_NoDup. apply H7_.  rewrite <-  uniqListNoDupEq. auto.
assert (equivList (mergeList' lst' (mergeList' lst l'0 decA) decA)  (mergeList' lst0 (mergeList' lst0' l'' decA) decA)).
apply IHPermutation2;auto.
rewrite  uniqListNoDupEq.
eapply Permutation_NoDup. apply H7_.  rewrite <-  uniqListNoDupEq. auto.    
eapply perm_trans.
apply H7. 
SearchAbout mergeList'.   
assert (Permutation  (mergeList' lst0' l'0 decA)  (mergeList' lst0' l'' decA)). 
eapply mergeListEquiv;auto. apply Permutation_refl.
eapply mergeListEquiv;auto. apply Permutation_refl. 
Qed. 



          

(*aux lemma for proving innerCombineEquiv'''*)
Lemma mergeConfigFuncEquivOnCom'': forall conf conf'  v0 v0' x y x' y' v x1,
uniqAllConf conf ->
uniqAllConf conf' ->
uniqAllConf x ->
uniqAllConf y -> 
uniqAllConf  v0 ->
uniqAllConf x' ->
uniqAllConf y' -> 
uniqAllConf  v0' ->
noDataConflict (datastate conf) (datastate x) (datastate v0) ->
noDataConflict (datastate conf) (datastate y) (datastate v) ->
noControlConflict (controlstate conf) (controlstate x) (controlstate v0) ->
noControlConflict (controlstate conf) (controlstate y) (controlstate v)  ->
noDataConflict (datastate conf') (datastate x') (datastate v0') ->
noDataConflict (datastate conf') (datastate y') (datastate v0') ->
noControlConflict (controlstate conf') (controlstate x') (controlstate v0') ->
noControlConflict (controlstate conf') (controlstate y') (controlstate v0')  ->
Result v = mergeConfigFunc conf x v0 ->
Result x1 = mergeConfigFunc conf y v  ->
equivConf conf conf' -> 
equivConf x x' ->
equivConf y y' ->
equivConf v0 v0' ->
dom (datastate conf) = dom (datastate x)->
dom (datastate conf) = dom (datastate y)->
dom (datastate conf) = dom  (datastate v0)->
dom (controlstate conf) = dom (controlstate x)->
dom (controlstate conf) = dom (controlstate y)->
dom (controlstate conf) = dom  (controlstate v0)->
dom (datastate conf') = dom (datastate x')->
dom (datastate conf') = dom (datastate y')->
dom (datastate conf') = dom  (datastate v0')->
dom (controlstate conf') = dom (controlstate x')->
dom (controlstate conf') = dom (controlstate y')->
dom (controlstate conf') = dom  (controlstate v0')->
(exists rc rc1, Result rc =  mergeConfigFunc conf' y' v0' /\
Result rc1 = mergeConfigFunc conf' x' rc /\
equivConf x1 rc1). 
Proof.
intros.  
unfold mergeConfigFunc in H15.
unfold mergeConfigFunc in H16.
unfold mergeConfigFunc.
 remember (mergeDataStateFunc (datastate conf) (datastate x) (datastate v0)).
destruct e. Focus 2. inversion H15.
remember (mergeControlStateFunc (controlstate conf) (controlstate x) (controlstate v0)).
destruct e. 
Focus 2. inversion H15.  
remember (mergeDataStateFunc (datastate conf) (datastate y) (datastate v)).
destruct e. Focus 2. inversion H16.
remember (mergeControlStateFunc (controlstate conf) (controlstate y) (controlstate v)).
destruct e. Focus 2. inversion H16. 
inversion H15. inversion H16.
unfold equivConf in H17.  
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. rewrite <- H17. 
  pose proof mergeDataStateFuncEquivOnCom'.
unfold uniqAllConf in H.  
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.  
remember H. clear Hequ.  
eapply H39 in H. Focus 2.  apply H21. Focus 2. apply H22.  Focus 2.
apply H23. Focus 2.  auto. Focus 2.   apply H8. 
Focus 2. rewrite H34. simpl. auto.  Focus 2.  apply Heqe1. 
destruct H. destruct H.  destruct H. destruct H44.
unfold equivConf in H18.
unfold equivConf in  H19.
unfold equivConf in H20. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.   
rewrite <- H19.
rewrite <-  H20. 
rewrite <- H.  
pose proof mergeControlStateFuncEquivOnCom'.  
eapply H58 in H43. Focus 2. apply H24. Focus 2. apply H25. Focus 2. apply H26.  Focus 2. apply H9.
Focus 2. apply H10. Focus 2. rewrite H34. simpl.  apply Heqe0. Focus 2.  
apply Heqe2. destruct H43. destruct H43.  destruct H43. rewrite <- H33. rewrite <- H50.  rewrite <- H46.
rewrite <- H43.                      
 (*prove control state first*)            
pose proof mergeListEquivOnCom''.
exists (  {|
    datastate := x0;
    controlstate := x3;
    raisedevents := mergeList' (raisedevents y') (raisedevents v0') raisedEvent_dec;
    exportedevents := mergeList' (exportedevents y') (exportedevents v0') raisedEvent_dec;
    finishedscenarios := mergeList' (finishedscenarios y') (finishedscenarios v0') scenario_dec;
    srcstatefinishedscenarios := mergeList' (srcstatefinishedscenarios y') (srcstatefinishedscenarios v0')
                                   scenarioState_dec;
    updatedvariableList := mergeList' (updatedvariableList y') (updatedvariableList v0') updatedVariable_dec;
    usedvariableList := mergeList' (usedvariableList y') (usedvariableList v0') usedVariable_dec |}).
simpl.   
rewrite <- H18. rewrite <- H44.  
rewrite <- H54. 
destruct H59.  
rewrite <- H59.   
exists ({|
    datastate := x2;
    controlstate := x4;
    raisedevents := mergeList' (raisedevents x')
                      (mergeList' (raisedevents y') (raisedevents v0') raisedEvent_dec) raisedEvent_dec;
    exportedevents := mergeList' (exportedevents x')
                        (mergeList' (exportedevents y') (exportedevents v0') raisedEvent_dec) raisedEvent_dec;
    finishedscenarios := mergeList' (finishedscenarios x')
                           (mergeList' (finishedscenarios y') (finishedscenarios v0') scenario_dec)
                           scenario_dec;
    srcstatefinishedscenarios := mergeList' (srcstatefinishedscenarios x')
                                   (mergeList' (srcstatefinishedscenarios y') (srcstatefinishedscenarios v0')
                                      scenarioState_dec) scenarioState_dec;
    updatedvariableList := mergeList' (updatedvariableList x')
                             (mergeList' (updatedvariableList y') (updatedvariableList v0') updatedVariable_dec)
                             updatedVariable_dec;
    usedvariableList := mergeList' (usedvariableList x')
                          (mergeList' (usedvariableList y') (usedvariableList v0') usedVariable_dec)
                          usedVariable_dec |}). 
simpl. split;auto. split;auto.
unfold equivConf. split. simpl.     
Print equivConf.    
Print mergeControlStateFunc. auto.
simpl. split;auto. 
split.     
rewrite H34.
simpl.   apply H60. unfold uniqAllConf in H1. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
unfold uniqAllConf in H2.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
unfold uniqAllConf in H4.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
unfold uniqAllConf in H5.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
unfold uniqAllConf in H3.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
unfold uniqAllConf in H6.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
auto. auto. auto.    

split. 
rewrite H34.
simpl. apply H60. unfold uniqAllConf in H1. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
unfold uniqAllConf in H2.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
unfold uniqAllConf in H4.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
unfold uniqAllConf in H5.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
unfold uniqAllConf in H3.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
unfold uniqAllConf in H6.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
auto. auto. auto. 
rewrite H34.
simpl. apply H60. unfold uniqAllConf in H1. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
unfold uniqAllConf in H2.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
unfold uniqAllConf in H4.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
unfold uniqAllConf in H5.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
unfold uniqAllConf in H3.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
unfold uniqAllConf in H6.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. auto.
auto. auto. auto. 
Qed.    


Definition domEqual (conf1 conf2:configuration):Prop:=
dom (datastate conf1)=dom (datastate conf2) /\ dom(controlstate conf1) = dom(controlstate conf2).

Lemma confEquivIn: forall l l' conf,
In conf l ->
confEquivList l l' ->
(exists conf', In conf' l' /\ equivConf conf conf').
Proof. intros. generalize dependent conf. 
induction H0.
- intros.  inversion H.
- intros.  destruct H1. rewrite <- H1. 
exists conf'. split. left;auto. auto. apply IHconfEquivList in H1.
destruct H1. destruct H1. exists x. split. right;auto. auto.    
- intros. destruct H2. rewrite <- H2. exists conf1'. split. right;left;auto. auto.
destruct H2. rewrite <- H2. exists conf2'. split. left;auto. auto.
apply IHconfEquivList in H2. destruct H2. destruct H2. exists x. split. right;right;auto. auto.         
- intros. apply IHconfEquivList1 in H. destruct H. destruct H.
apply IHconfEquivList2 in H. 
destruct H. destruct H. exists x0. split;auto.
eapply equivConf_Trans. apply H0. apply H1.    
Qed.           


Lemma confEq_uniq': forall l l', 
uniqList l ->
(forall conf' conf'', In conf' l -> In conf'' l -> conf' <> conf'' -> ~(equivConf conf' conf'')) ->
confEquivList l l' ->
uniqList l' /\ (forall conf' conf'', In conf' l' -> In conf'' l' -> conf' <> conf'' -> ~(equivConf conf' conf'')).
Proof.
intros.    induction H1.
- split.  constructor. intros. inversion H1.
- split. 
+ constructor. inversion H;subst.
apply IHconfEquivList in H5. destruct H5;auto.
intros. apply H0. right;auto. right;auto. auto.
unfold not. intros. 
pose proof confEquivIn.
apply H4 with (l':=l) in H3. Focus 2. SearchAbout confEquivList.   apply confEquivList_sym.
auto.
destruct H3. destruct H3. apply equivConf_Sym in H5.   
destruct H0 with (conf':=x) (conf'':=conf);auto. right;auto. left;auto. inversion H. subst.
unfold not. intros. rewrite H6 in H3. exfalso;apply H9;auto. rewrite equivConf_Sym.
eapply equivConf_Trans. apply H1. apply equivConf_Sym. auto.
+ 
intros. destruct H3. destruct H4. rewrite H4 in H3. exfalso;apply H5;auto. unfold not; intros.
subst.  
inversion H;subst.
pose proof confEquivIn.
apply H3 with (l':=l) in H4. Focus 2. SearchAbout confEquivList.   apply confEquivList_sym.
auto. destruct H4. destruct H4. destruct H0 with (conf':=conf) (conf'':=x).
left;auto. right;auto. unfold not.  intros. rewrite H10 in H9. exfalso;apply H9;auto.
eapply equivConf_Trans. 
apply H1. eapply equivConf_Trans. apply H6.  auto.
destruct H4. subst. unfold not. intros.   
pose proof confEquivIn.
apply H6 with (l':=l) in H3. Focus 2. SearchAbout confEquivList.   apply confEquivList_sym.
auto. destruct H3. destruct H3. destruct H0 with (conf':=conf) (conf'':=x).
left;auto. right;auto. unfold not.  intros. rewrite <- H8 in H3. inversion H. subst.
exfalso;apply H12;auto. 
eapply equivConf_Trans. 
apply H1. eapply equivConf_Trans. apply equivConf_Sym.  apply H4.
auto.  
inversion H;subst.  
apply IHconfEquivList in H8;auto.  Focus 2. intros. apply H0. right;auto. right;auto. auto.
destruct H8. apply H7. auto. auto. auto.
- inversion H;subst. inversion H6;subst.
split. constructor. constructor. apply IHconfEquivList in H8. destruct H8. auto.
intros. apply H0. right;right;auto. right;right;auto. auto. unfold not. intros.
pose proof confEquivIn.
apply H5 with (l':=l) in H4.   Focus 2. SearchAbout confEquivList.   apply confEquivList_sym.
auto. destruct H4. destruct H4. destruct H0 with (conf':=conf1) (conf'':=x).
left;auto.  right;right;auto. unfold not.  intros. rewrite H11 in H7. apply H7. right;auto.
eapply equivConf_Trans. 
apply H1. auto.  
unfold not.  intros. destruct H4. destruct H0 with (conf':=conf1) (conf'':=conf2).
left;auto. right;left;auto. unfold not. intros. rewrite H5 in H7. apply H7. left;auto.
rewrite H4 in H1. eapply equivConf_Trans. apply H1. apply equivConf_Sym. auto.
pose proof confEquivIn.
apply H5 with (l':=l) in H4.   Focus 2. SearchAbout confEquivList.   apply confEquivList_sym.
auto. destruct H4. destruct H4. destruct H0 with (conf':=conf2) (conf'':=x).
right;left;auto.  right;right;auto. unfold not.  intros. rewrite H11 in H9. exfalso;apply H9;auto. 
eapply equivConf_Trans. apply H2. auto.
intros.   
destruct H4.
destruct H5.
rewrite H5 in H4. exfalso;apply H10;auto.
destruct H5. rewrite <- H4 in H10. rewrite <- H5 in H10. 
assert (~equivConf conf1 conf2).
apply H0;auto. left;auto. right;left;auto.
unfold not. intros. rewrite H11 in H7. apply H7. left;auto.
unfold not.  intros. apply H11.
rewrite <- H4 in H12. rewrite <- H5 in H12. 
 eapply equivConf_Trans. apply H1. 
apply equivConf_Sym in H1. eapply equivConf_Trans.
apply equivConf_Sym. apply H12. apply equivConf_Sym. auto.
pose proof confEquivIn.
apply H11 with (l':=l) in H5. Focus 2. SearchAbout confEquivList.   apply confEquivList_sym.
auto. destruct H5. destruct H5. rewrite <- H4.
assert (~(equivConf conf2 x)). apply H0.     
right;left;auto. right;right;auto. unfold not. intros. rewrite H13 in H9.    exfalso;apply H9;auto.
unfold not. intros. apply H13. 
apply equivConf_Sym. apply equivConf_Sym in H12.   
eapply equivConf_Trans. apply H12.  apply equivConf_Sym in H14.   
eapply equivConf_Trans. apply H14. apply equivConf_Sym. auto.
destruct H4. destruct H5.                              
 
assert (~equivConf conf1 conf2).
apply H0;auto. left;auto. right;left;auto.
unfold not. intros. rewrite H11 in H7. apply H7. left;auto.
unfold not.  intros. apply H11.
rewrite <- H4 in H12. rewrite <- H5 in H12. 
 eapply equivConf_Trans. apply H1. 
apply equivConf_Sym in H1. eapply equivConf_Trans.
apply H12. apply equivConf_Sym. auto. 
destruct H5. rewrite <- H4 in H10. rewrite <- H5 in H10. exfalso;apply H10;auto.

pose proof confEquivIn.
apply H11 with (l':=l) in H5. Focus 2. SearchAbout confEquivList.   apply confEquivList_sym.
auto. destruct H5. destruct H5. rewrite <- H4.
assert (~(equivConf conf1 x)). apply H0.     
left;auto. right;right;auto. unfold not. intros. rewrite H13 in H7. apply H7. right;auto.   
unfold not. intros. apply H13. 
apply equivConf_Sym. apply equivConf_Sym in H12.   
eapply equivConf_Trans. apply H12.  apply equivConf_Sym in H14.   
eapply equivConf_Trans. apply H14. apply equivConf_Sym. auto.

destruct H5.
pose proof confEquivIn.
apply H11 with (l':=l) in H4. Focus 2. SearchAbout confEquivList.   apply confEquivList_sym.
auto. destruct H4. destruct H4. rewrite <- H5.
assert (~(equivConf conf2 x)). apply H0.     
right;left;auto. right;right;auto. unfold not. intros. rewrite H13 in H9. exfalso;apply H9;auto.  
unfold not. intros. apply H13. 
apply equivConf_Sym. apply equivConf_Sym in H12.   
eapply equivConf_Trans. apply H12.   
eapply equivConf_Trans. apply H14. apply equivConf_Sym. auto.

destruct H5.
pose proof confEquivIn.
apply H11 with (l':=l) in H4. Focus 2. SearchAbout confEquivList.   apply confEquivList_sym.
auto. destruct H4. destruct H4. rewrite <- H5.
assert (~(equivConf conf1 x)). apply H0.     
left;auto. right;right;auto. unfold not. intros. rewrite H13 in H7. apply H7. right;auto.   
unfold not. intros. apply H13. 
apply equivConf_Sym. apply equivConf_Sym in H12.   
eapply equivConf_Trans. apply H12.   
eapply equivConf_Trans. apply H14. apply equivConf_Sym. auto.

apply  IHconfEquivList in H8. destruct H8. 
apply H11;auto. intros. apply H0;auto. right;right;auto. right;right;auto.

-  apply IHconfEquivList2.
assert ( uniqList l0 /\  (forall conf' conf'' : configuration,  In conf' l0 -> In conf'' l0 -> conf' <> conf'' -> ~ equivConf conf' conf'')).
apply IHconfEquivList1.
auto. apply H0. destruct H1. auto. 
assert ( uniqList l0 /\  (forall conf' conf'' : configuration,  In conf' l0 -> In conf'' l0 -> conf' <> conf'' -> ~ equivConf conf' conf'')).
apply IHconfEquivList1.
auto. apply H0. destruct H1. auto.
Qed.  

(*aux lemma for proving syncEquiv'*)
Lemma innerCombineEquiv''':forall conf conf' lst lst' conf1,
uniqList lst ->
uniqList lst' ->
confEquivList lst lst' ->
equivConf conf conf' ->
Result conf1 =  innerCombineFunc' conf None lst ->
uniqAllConf conf ->
uniqAllConf conf' ->
(forall conf1, In conf1 lst -> uniqAllConf conf1  /\  domEqual conf1 conf) ->
(forall conf2, In conf2 lst' -> uniqAllConf conf2 /\  domEqual conf2 conf') ->
(forall conf1 conf1', In conf1 lst -> In conf1' lst -> noConflict conf conf1 conf1') ->
(forall conf2 conf2', In conf2 lst' -> In conf2' lst' -> noConflict conf' conf2 conf2') ->
(exists conf2, Result conf2 =  innerCombineFunc' conf' None lst' /\
equivConf conf1 conf2). 
  
Proof.
intros. generalize dependent conf1. generalize dependent conf.  
generalize dependent conf'.
induction H1.
- intros.  simpl in H3. inversion H3.
- intros. simpl. simpl in H10. 
inversion H;subst. inversion H0;subst. destruct l.
+ simpl in H10. inversion H10. destruct l'0. simpl. exists conf'. split;auto.
SearchAbout confEquivList.  assert (~confEquivList Datatypes.nil (c :: l'0)). apply confEquivList_cons_nil.
exfalso;apply H11;auto.  
+ destruct l'0.     
assert (confEquivList nil (c::l)).
apply  confEquivList_sym. auto.
assert (~confEquivList Datatypes.nil (c :: l)).
apply confEquivList_cons_nil. exfalso;apply H12;auto.
simpl in H10.       
remember (innerCombineFunc' conf0 (Some c) l ).
destruct e. Focus 2. inversion H10.
remember H3. clear Heqe0. apply IHconfEquivList with (conf1:=v) in e.
destruct e. destruct H11. 
simpl. simpl in H11. rewrite <- H11. 
SearchAbout mergeConfigFunc.  
eapply mergeConfigEquiv in H10. Focus 2. apply H3. Focus 2. apply H1. Focus 2. apply H12.
apply H10. auto. auto. auto.  intros. split;auto.   
destruct H7 with conf2. right;auto. auto. destruct H7 with conf2. right;auto. auto. 
intros. destruct H9 with (conf2:=conf2) (conf2':=conf2'). right;auto. right;auto.
unfold noConflict. split;auto.   
auto. 
intros.   destruct H6 with conf2. right;auto. auto. 
intros.   destruct H8 with (conf1:=conf2) (conf1':=conf1'). right;auto. right;auto.
unfold noConflict. split;auto.   
 simpl. auto. 
- intros. simpl in H11.  
remember (innerCombineFunc' conf (Some conf2) l). 
destruct e. Focus 2. inversion H11. 
simpl. destruct l. simpl in Heqe. inversion Heqe. destruct l'0. simpl. 
rewrite H13 in H11. 
SearchAbout mergeConfigFunc.       
eapply mergeConfSwitchInvariant''. Focus 12. apply H4. Focus 12. apply H1. Focus 12. apply H2.
auto. auto. auto. destruct H8 with conf1. left;auto. auto. destruct H8 with conf2. right;left;auto. auto. 
destruct H7 with conf1'. right;left;auto. auto. destruct H7 with conf2'. left;auto. auto. unfold uniqAllConf in H6.
destruct H6;auto. destruct H10 with (conf3:=conf1) (conf1':=conf2).
left;auto. right;left;auto. auto.      
destruct H6;auto. destruct H10 with (conf3:=conf1) (conf1':=conf2).
left;auto. right;left;auto. auto.
 destruct H9 with (conf2:=conf1') (conf2'0:=conf2').
right;left;auto. left;auto. auto.      
 destruct H9 with (conf2:=conf1') (conf2'0:=conf2').
right;left;auto. left;auto. auto.   
assert (~confEquivList Datatypes.nil (c :: l'0)).
apply confEquivList_cons_nil. exfalso;apply H12;auto. 
destruct l'0. 
assert (confEquivList Datatypes.nil (c :: l) ).
apply confEquivList_sym;auto.
assert (~confEquivList Datatypes.nil (c :: l)).
apply confEquivList_cons_nil. exfalso;apply H13;auto.
simpl in Heqe.
simpl.  
remember (innerCombineFunc' conf (Some c) l).
destruct e. Focus 2. inversion Heqe.
remember H4. clear Heqe1. apply IHconfEquivList with (conf1:=v0) in e.
destruct e. destruct H12. 
simpl.  simpl in H12. rewrite <- H12. 
SearchAbout mergeConfigFunc. 
remember (mergeConfigFunc conf' conf1' x).
destruct e.
remember (mergeConfigFunc conf' conf2' v1).
destruct e.
 pose proof mergeConfigFuncEquivOnCom''.
apply H14  with (conf':=conf') (v0:=v0) (x:=conf2) (v0':=x) (y':=conf1') (x':=conf2')  in H11;auto.  
destruct H11. destruct H11. destruct H11.  destruct H15.    rewrite <- H11 in Heqe1. inversion Heqe1. 
rewrite  H18 in Heqe2. rewrite <- H15 in Heqe2. inversion Heqe2.        
exists x1. split;auto. destruct H8 with conf2. right;left;auto. auto.  destruct H8 with conf1. left;auto. auto.
Print uniqAllConf. 

admit. destruct H7 with conf2'. left;auto. auto.  destruct H7 with conf1'. right;left;auto. auto.
admit. admit. admit. admit. admit. admit. admit. admit. admit. 
destruct H8 with conf2. right;left;auto. unfold domEqual in H16. destruct H16;auto. 
 destruct H8 with conf1. left;auto. unfold domEqual in H16. destruct H16;auto.
admit.
destruct H8 with conf2. right;left;auto. unfold domEqual in H16. destruct H16;auto. 
 destruct H8 with conf1. left;auto. unfold domEqual in H16. destruct H16;auto.
admit.
destruct H7 with conf2'. left;auto. unfold domEqual in H16. destruct H16;auto. 
 destruct H7 with conf1'. right;left;auto. unfold domEqual in H16. destruct H16;auto.
admit. 
destruct H7 with conf2'. left;auto. unfold domEqual in H16. destruct H16;auto. 
 destruct H7 with conf1'. right;left;auto. unfold domEqual in H16. destruct H16;auto.
admit.        
             
 Focus 3. inversion H. inversion H14;auto. Focus 3.     inversion H0. inversion H14. auto. Focus 3.
auto. Focus 5. auto. Focus 3. intros. destruct H7 with conf3. right;right;auto. split. auto. auto.   
Focus 3. intros. apply H9. right;right;auto. right;right;auto. Focus 3. intros. destruct H8 with conf3. right;right;auto.
split;auto. Focus 3. intros. apply H10;auto. right;right;auto. right;right;auto.
Focus 3. simpl;auto.              
 pose proof mergeConfigFuncEquivOnCom''.
apply H14  with (conf':=conf') (v0:=v0) (x:=conf2) (v0':=x) (y':=conf1') (x':=conf2')  in H11;auto.          
destruct H11. destruct H11. destruct H11.  destruct H15. rewrite <- Heqe1 in H11.  inversion H11. rewrite <- H18 in Heqe2.
 rewrite <- H15 in Heqe2. inversion Heqe2. Focus 27. 
pose proof mergeConfigFuncEquivOnCom''.
apply H14  with (conf':=conf') (v0:=v0) (x:=conf2) (v0':=x) (y':=conf1') (x':=conf2')  in H11;auto.          
destruct H11. destruct H11. destruct H11.  destruct H15. rewrite <- Heqe1 in H11.  inversion H11. 
destruct H8 with conf2. right;left;auto. auto.
destruct H8 with conf1. left;auto. auto.
admit.
destruct H7 with conf2'. left;auto. auto. 
destruct H7 with conf1'. right;left;auto. auto. 
admit.
admit. admit. admit. admit. admit. admit. admit. admit.
destruct H8 with conf2. right;left;auto. destruct H16;  auto.
destruct H8 with conf1. left;auto. destruct H16;  auto.
admit.
destruct H7 with conf2'. left;auto. destruct H16; auto. 
destruct H7 with conf1'. right;left;auto. destruct H16; auto.
 destruct H8 with conf2. right;left;auto. destruct H16;  auto.
destruct H8 with conf2. right;left;auto. destruct H23; auto.
destruct H8 with conf1. left;auto. destruct H16;  auto.
admit. 
destruct H7 with conf2'. left;auto. destruct H16; auto. 
destruct H7 with conf1'. right;left;auto. destruct H16; auto.
admit. 
destruct H7 with conf2'. left;auto. destruct H16; auto. 
destruct H7 with conf1'. right;left;auto. destruct H16; auto.
admit.
destruct H8 with conf2. right;left;auto. auto.
destruct H8 with conf1. left;auto. auto.
admit.
destruct H7 with conf2'. left;auto. auto. 
destruct H7 with conf1'. right;left;auto. auto. 
admit.
admit. admit. admit. admit. admit. admit. admit. admit.
destruct H8 with conf2. right;left;auto. destruct H16;  auto.
destruct H8 with conf1. left;auto. destruct H16;  auto.
admit.
destruct H7 with conf2'. left;auto. destruct H16; auto. 
destruct H7 with conf1'. right;left;auto. destruct H16; auto.
 destruct H8 with conf2. right;left;auto. destruct H16;  auto.
destruct H8 with conf2. right;left;auto. destruct H23; auto.
destruct H8 with conf1. left;auto. destruct H16;  auto.
admit. 
destruct H7 with conf2'. left;auto. destruct H16; auto. 
destruct H7 with conf1'. right;left;auto. destruct H16; auto.
admit. 
destruct H7 with conf2'. left;auto. destruct H16; auto. 
destruct H7 with conf1'. right;left;auto. destruct H16; auto.
admit.
- intros.        
assert ( exists conf2 : configuration,
                     Result conf2 = innerCombineFunc' conf' None l0 /\ equivConf conf1 conf2).
apply IHconfEquivList1 with conf;auto. SearchAbout confEquivList.   auto.   admit.
intros. admit. intros. admit.     
 destruct H1. destruct H1. 
SearchAbout innerCombineFunc'.   
eapply innerCombineEquiv' in H1.  Focus 2. apply equivConf_Sym. apply H2.    
destruct H1. destruct H1. apply IHconfEquivList2 with (conf:=conf);auto.
SearchAbout confEquivList.     Check innerCombineEquiv'. 
pose proof confEq_uniq'.
remember  H. clear Hequ.
apply H12 with (l':=l0) in u. destruct u. auto. Focus 2. auto.  
admit.  Focus 3.  auto.     
 (*
Focus 2. apply equivConf_Sym. apply H2.
eapply IHconfEquivList2 in H1. Focus 4. apply H2. destruct H1.
destruct H1. exists x1. split;auto. eapply equivConf_Trans. apply H4. eapply equivConf_Trans. apply H5. auto.   *)         
Admitted.

Lemma innerCombineKeepuniqAllConf: forall conf l  v,
uniqAllConf conf ->
(forall conf', In conf' l -> uniqAllConf conf') ->
Result v = innerCombineFunc' conf None l ->
uniqAllConf v. 
Proof. 
Admitted. 

Lemma mergeConfigNoDataConflict: 
forall v  conf conf1 conf2, 
Result v = mergeConfigFunc conf conf1 conf2 ->
noDataConflict (datastate conf) (datastate conf1) (datastate conf2). 
Proof.
Admitted. 
     


(*aux lemma for proving weakconfluence below*)
(*given the same event, two equivalent configruations will step to two equivalent configurations*)
Lemma syncEquiv': forall conf conf' conf1  e,
equivConf conf conf' ->
synchrony conf conf1 e ->
correct_configuration conf ->
(exists conf2, synchrony conf' conf2 e /\
equivConf conf1 conf2).  
Proof.
intros. unfold synchrony in H0.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. 
unfold combineFunc in H4.
assert (checkType conf e = checkType conf' e).
admit.     
remember (checkType conf e). 
destruct b.
Focus 2. inversion H4. 
remember (constructConfigList (dom (controlstate conf)) e conf ).
destruct e0. Focus 2. inversion H4. 
destruct v. inversion H4. 
unfold constructConfigList in Heqe0. 
unfold synchrony. unfold combineFunc.
remember (checkType conf' e). destruct b.  Focus 2. inversion H5.
clear H5. clear Heqb0. 
unfold constructConfigList.
remember  ( (transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec) e conf)).
destruct l. simpl in Heqe0.  inversion Heqe0.  
remember H. clear Heqe1. unfold equivConf in e0.  
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
rewrite <- H6.  

remember ( (transformConfig (filterList (finishedscenarios conf') (dom (controlstate conf)) scenario_dec) e conf')).
destruct l0. 
assert (Permutation (transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec) e conf)
   (transformConfig (filterList (finishedscenarios conf') (dom (controlstate conf)) scenario_dec) e conf')).
apply transformEquiv. auto. 
apply filterListEquiv. auto. remember H10. clear Heqp.   rewrite <- Heql in H10.  rewrite <- Heql0 in H10.  
assert  (~Permutation nil (s::l)). apply Permutation_nil_cons.  apply Permutation_sym in H10. exfalso;apply H11;auto.
assert (Permutation (s::l) (s0::l0)).
rewrite Heql. rewrite Heql0. apply transformEquiv. auto. apply filterListEquiv. auto.

pose proof constructListEquiv. remember H. clear Heqe1. 
eapply H11 in e0. 
Focus 2. apply H10 . Focus 2. apply Heqe0. Focus 2.     
destruct H1. (*uniqList (s :: l)*)  admit.
destruct e0. destruct H12. rewrite <- H12. 
destruct x. SearchAbout confEquivList. apply confEquivList_sym in H13.
assert (~ confEquivList nil (c::v)). apply confEquivList_cons_nil. exfalso;apply H14;auto. (*inversion H13. destruct H14 with c. left;auto. destruct H16;inversion H16.  *)    
pose proof innerCombineEquiv'''. 
remember H4. clear Heqe1. symmetry in e0. eapply H14 in e0. destruct e0.
destruct H15. Focus 2. admit.   Focus 2. admit.  Focus 2.   apply H13. Focus 2 . apply H. exists x0.         
split. 
split. 
unfold equivConf in H.      
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
         eapply Permutation_in.
apply H7. auto.   
split.
unfold not ;intros.
unfold ErrConfig in H2. unfold not in H2. apply H2.
intros.  unfold ErrConfig in H17. assert (In e (raisedevents conf')).   eapply Permutation_in. apply H7. auto.   
  apply H17 in H19. destruct H19. 
 SearchAbout constructConfigList'.    
eapply constructConfigListEquiv. apply equivConf_Sym. apply H.
unfold  constructConfigList in H19. rewrite  Heql in H10.  rewrite Heql0 in H10. apply Permutation_sym.
apply H10.  unfold constructConfigList in H19. rewrite <- H6 in H19. apply H19. 
split. unfold not.  intros. unfold not in H3. apply H3. unfold conflict in H17.
destruct H17.             
destruct H17.
destruct H18.
destruct H18.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
unfold conflict.  
 unfold constructConfigList in H17. 
unfold  constructConfigList. 
Print noConflict. 
Print noDataConflict. 
pose proof constructListEquiv.
+ 
remember H. clear Heqe1.
assert (equivConf conf' conf).
apply equivConf_Sym. auto.   
eapply H21 in H22. Focus 2.
assert (equivList 
(transformConfig (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec) e conf')   
((transformConfig (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec) e conf))).
apply transformEquiv. apply  equivConf_Sym. auto.
Check filterListEquiv.
unfold equivConf in e0. destruct e0. destruct H24.
rewrite <- H24.       
 apply filterListEquiv. destruct H25. destruct H26.  apply Permutation_sym. auto.
apply H23. Focus 2. symmetry in H17. apply H17.
destruct H22.  destruct H22. 
exists x4. split. 
symmetry. auto.  SearchAbout confEquivList.  
(*unfold  confEquivList in H23.
destruct H23.
apply H23 in H18.
apply  H23 in H19.
destruct H18. 
destruct H19.
exists x5. exists x6.
destruct H18. destruct H19. split;auto.
split;auto.
unfold noConflict in H20. 
unfold noConflict.
unfold equivConf in e0.    
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
rewrite  H29.
rewrite H30.
unfold equivConf in H25. 
unfold equivConf in H26.   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
rewrite <- H25.
rewrite <- H26.
rewrite <- H34.
rewrite <- H38.*)
auto. admit.  admit. admit. 
+ auto.
+ auto. 
Admitted.  
    

(*correctness of multiple steps*)
Lemma chainMergeCorrectness: forall conf conf' n,
correct_configuration conf -> 
 chainMergeWithEventList conf conf' n ->
correct_configuration conf'. 
Proof. intros. induction H0. eapply termL5. apply H. apply H0. 
     eapply termL5. apply IHchainMergeWithEventList in H. apply H.
apply H1.   
Qed. 

(*aux lemma to prove weakconfluence*)
(*if two events are interference-free, then theire execution is not interference with each other*)
Lemma diamond: forall conf conf1 conf2  e1 e2,
interference_free conf (eventDefinition e1) (eventDefinition e2) 
-> correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 -> 
(exists conf'1 conf'2, synchrony conf1 conf'1 e2
/\ synchrony conf2 conf'2 e1
/\ equivConf conf'1 conf'2). 
Proof. Admitted. 

(*aux lemma *)
(*two pending events are independent under deter_property*)
Lemma raisedEventsInd: forall conf e1 e2,
 deter_property conf ->
In e1 (raisedevents conf) -> 
In e2 (raisedevents conf) ->
(exists conf', synchrony conf conf' e1) ->
(exists conf'', synchrony conf conf'' e2) ->
interference_free conf (eventDefinition e1) (eventDefinition e2) . 
Proof. Admitted. 


(*aux lemma to prove confluence*)
(*from a configuration conf, if it can step 1 steps to conf1 and n steps to conf2, then conf1 and
conf2 can respectively step m steps and 1 step to conf1' and conf2' which are equivalent*)
(*structure of the proof is finished by induction on n*)
(*need to result of diamond*)
Lemma weakconfluence: forall  n2 conf conf1 conf2 ,
correct_configuration conf  ->
 deter_property conf ->
 noCyclicCausalRelation conf -> 
chainMergeWithEventList conf conf1 1 ->
chainMergeWithEventList conf conf2 n2 ->
(exists conf1' conf2' n3  , chainMergeWithEventList conf1 conf1' n3 
/\ chainMergeWithEventList conf2 conf2' 1  /\ equivConf conf1' conf2').
Proof. intro n2. induction n2.

- intros. inversion H3.
- intros. inversion H3;subst.  inversion H2. subst. 
pose proof diamond. pose proof raisedEventsInd.
Print deter_property.  
assert (interference_free conf (eventDefinition e0) (eventDefinition e)).
apply H6;auto. unfold synchrony in H4;destruct H4;auto.   unfold synchrony in H7;destruct H7;auto.
exists conf1;auto. exists conf2;auto.
apply H5 with (conf1:=conf1) (conf2:=conf2) in H8.  destruct H8. destruct H8. 
 destruct H8. destruct H9. exists x. exists x0. exists 1. split. apply basic_case''' with e. auto.
split. apply basic_case''' with e0. auto.  auto. auto. auto. auto.    subst. 
inversion H5.  remember H. clear Heqc.   apply IHn2 with (conf1:=conf1) (conf2:=conf') in H. Focus 2. auto. Focus 2. auto. Focus 2.
auto. Focus 2. auto. destruct H. 
destruct H. destruct H. destruct H.  destruct H4. 
inversion H4;subst. Focus 2. inversion H9.

               pose proof diamond. 
assert ( interference_free conf' (eventDefinition e) (eventDefinition e0)).
admit. apply H9 with (conf1:= conf2) (conf2:=x0) in H10.
destruct H10;
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
Focus 3. auto. Focus 3. auto.
destruct H10.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. 
pose proof syncEquiv'. assert (equivConf x0 x). rewrite  equivConf_Sym. auto.  apply H13 with (conf1:= x3)(e:=e) in H14.
destruct H14. destruct H14.     
exists x4. exists x2. exists (S x1). split.
eapply inductive_case'''. apply H. apply H14. split. apply basic_case''' with e0. auto. 
Focus 2.  auto.  assert (equivConf x2 x4). eapply equivConf_Trans. apply H12;auto. auto. 
rewrite  equivConf_Sym. auto. 
eapply chainMergeCorrectness. eapply chainMergeCorrectness. apply c. apply H5.
apply H4. eapply  chainMergeCorrectness. apply c. apply H5.       
Admitted.

(*aux lemma to prove determinism*)
(*from a configuration conf, if it can step n1 steps to conf1 and n2 steps to conf2, then conf1 and
conf2 can respectively step n3 steps and n4 steps back to conf1' and conf2' which are equivalent*)
(*structure of the proof is finished using weak confluence*)
Lemma confluence: forall  n1 n2 conf conf1 conf2 ,
correct_configuration conf  ->
 deter_property conf ->
 noCyclicCausalRelation conf -> 
chainMergeWithEventList conf conf1 n1 ->
chainMergeWithEventList conf conf2 n2 ->
(exists conf1' conf2' n3 n4  , chainMergeWithEventList conf1 conf1' n3 
/\ chainMergeWithEventList conf2 conf2' n4  /\ equivConf conf1' conf2').
Proof. intro n1.  induction n1.
- intros. inversion H2.
-  intros. inversion H2;subst. pose proof weakconfluence. 
apply H4 with (n2:=n2) (conf1:=conf1) (conf2:=conf2) in H.       Focus 2.
auto. Focus 2. auto. Focus 2. auto. Focus 2. auto. 
destruct H. destruct H. destruct H.  
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
exists x. exists x0. exists x1. exists 1. split;auto. 
remember H. clear Heqc.
apply IHn1 with (n2:=n2) (conf1:=conf') (conf2:=conf2) in H. 
Focus 2. auto. Focus 2. auto. Focus 2. auto. Focus 2. auto.
pose proof weakconfluence. assert (correct_configuration conf').
 apply chainMergeCorrectness with (conf:=conf) (n:=n1). auto. auto. 
remember H6. clear Heqc0.  
destruct H. 
destruct H.
destruct H.
destruct H. 
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.      
apply H4 with (conf1:=conf1) (conf2:=x) (n2:=x1)  in c0.
Focus 2. admit. Focus 2. admit. Focus 2. apply basic_case''' with e. auto. 
Focus 2. auto. 
destruct c0. 
destruct H10.
destruct H10.    


    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
 exists x3. 
inversion H11;subst. Focus 2. inversion H14.    
pose proof syncEquiv'. apply H14 with  (conf1:=x4) (e:=e0)  in H9. 
Focus 2. auto.  destruct H9. destruct H9.        
exists x6. exists x5.  exists (S x2).
split. auto. split. eapply inductive_case'''. apply H7. apply H9.
eapply equivConf_Trans. apply H12. auto.          
eapply  chainMergeCorrectness. apply H6. apply H.  
  
Admitted.                  

(*aux lemma, if conf can move n steps to conf1, then there is a conf' that conf can move one step to*)
Lemma chainSyncExists': forall conf conf1 n, 
chainMergeWithEventList conf conf1 n ->
(exists conf' e, synchrony conf conf' e).
Proof. intros.
induction H. exists conf'. exists e. auto.
intros. destruct IHchainMergeWithEventList. destruct H1.
exists x. exists x0. auto.
Qed.  

(*determinism thoerem*)
(*proved using confluence*)
Theorem deterministicMacroStep: forall conf conf1 conf2 n1 n2,
 initialConfig conf  ->
 deter_property conf ->
 noCyclicCausalRelation conf -> 
chainMergeWithEventList conf conf1 n1 ->
chainMergeWithEventList conf conf2 n2 ->
stuckConfig conf1 ->
stuckConfig conf2 ->
equivConf conf1 conf2. 
Proof.
intros.
pose proof  confluence. unfold initialConfig in H. destruct H.    apply H6  with (n1:=n1) (n2:=n2) (conf1:= conf1) (conf2:=conf2) in H.  
destruct H. destruct H.    
destruct H.
destruct H. 
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. Focus 2. auto. Focus 2. auto. Focus 2. auto. Focus 2. auto.
unfold stuckConfig in H4.  pose proof chainSyncExists'. apply H12 in H.
destruct H. destruct H. destruct H4 with x4. Focus 2. exists x3. auto. 
unfold synchrony in H. destruct H;auto.        
     
Qed.         

