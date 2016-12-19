(*aux lemmas on common datastructure*)
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
Set Implicit Arguments.
Set Boolean Equality Schemes.
(*Definition of error messages, will reorganize later*)
Definition error0 : string := "error".

Definition error1: string := "no scenario state specified".

Definition error2: string := "evaluation error".

Definition error3: string := "no event instance".

Definition error4: string := "no step".

Definition error5: string := "type not matched".

Definition error6: string := "not matched".

Definition error7: string := "scenario not matched". 

Definition error8: string := "no conf". 

Definition error9: string := "no update". 

Definition error10: string := "state non-determinism".

Definition error11: string := "data non-determinism".

Definition error12: string := "number of list not matched".

(*exluded middle is used to prove some lemmas*)
Axiom excluded_middle: forall P1, P1 \/ ~ P1.
(*each scenario has its own unique name*)
Axiom ScenarioEquivalence: forall sce1 sce2, (scenarioId sce1) = (scenarioId sce2) <-> sce1 = sce2. 
(*each event has its own unique name*)
Axiom EventEquivalence: forall ev1 ev2, (eventId ev1) = (eventId ev2) <-> ev1 = ev2. 


(*aux definition and lemmas for proving listInclusion*)
Inductive repeats {X:Type} : list X -> Prop :=
| brepeat : forall  (x:X) (l1: list X), In x l1 -> repeats (x::l1)
| repe: forall (x: X) (l1: list X), repeats l1 -> repeats (x::l1).

Lemma repeatUniq: forall {A:Type} (lst: list A), repeats lst <-> ~(uniqList lst).
Proof. split.
- intros. induction H. unfold not. intros. inversion  H0. subst. unfold not in H4. apply H4 in H. auto. 
  unfold not.  intros. inversion H0. subst. unfold not in  IHrepeats. apply  IHrepeats in H3. inversion H3.
- intros. induction lst.  assert (@uniqList A Datatypes.nil). apply uniqL_nilL. unfold not in H. apply H in H0. inversion H0. 
assert (In a lst \/ ~ In a lst). apply excluded_middle. destruct H0. apply brepeat. auto.
    apply repe. apply IHlst. unfold not. intros. unfold not in H. apply H. apply uniqL_push. auto. auto.
Qed. 

Lemma in_1: forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1, exists l2, l = app l1  (x::l2).
Proof.
  intros. induction l.
  inversion H. inversion H.
  exists nil. exists l. simpl. rewrite H0.  reflexivity.
  apply IHl in H0. destruct H0. destruct H0.
 rewrite H0. exists (a::x0). simpl. exists x1. reflexivity. 
Qed.

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X),
     In x (xs ++ ys) -> In x xs \/ In x ys.
Proof. intros X xs. induction xs.
-  intros. right. simpl in H. auto.
- intros. simpl in H.  destruct H.  
+ left. simpl. left. auto.
+  simpl. assert ( ((In x xs) \/ In x ys) -> (a = x \/ In x xs) \/ In x ys). intros.
destruct H0. left. right. auto. right. auto. apply H0. apply IHxs. auto.
Qed.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X),
     In x xs \/ In x ys -> In x (xs ++ ys).  
Proof. 
intros X xs. induction xs.
- intros. destruct H. inversion H. simpl. auto.
- intros. simpl. simpl in H.  
assert ( (a = x \/  (In x xs \/ In x ys))). destruct H. destruct H. left. auto.
right. left. auto. right. right. auto. destruct H0. left. auto.
right. apply IHxs. auto.
Qed.           
           


Lemma contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros p q contra.
  inversion contra as [HP HNP].
  unfold not in HNP.  (* Dragan: novo *)
  apply HNP in HP.
  inversion HP.
Qed.

Local Close Scope Z_scope.
Local Close Scope N_scope.
Local Close Scope Q_scope.

Lemma pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1']; intros.
   inversion H0.
pose proof excluded_middle. 
   destruct (H1 (In x l1')). 
   apply brepeat. apply H2. apply repe.
   destruct (H1 (In x l2)). apply in_1 in H3.
   inversion H3. inversion H4.
   apply IHl1' with (l2:=(app x0  x1)).
intros. destruct (H1 (x = x2)). subst. contradiction. 
  assert (In x2 (x::l1') ). simpl. right. auto. apply H in H8. rewrite H5 in H8. 
apply appears_in_app in H8.  apply  app_appears_in. destruct H8.
left. auto.  simpl in H8. destruct H8. unfold not in H7. exfalso. apply H7; auto.
right. auto.
rewrite H5 in H0. rewrite app_length in H0. simpl in H0. 
rewrite <- plus_n_Sm in H0.   rewrite app_length. omega.   
apply contradiction_implies_anything with (P:=In x l2). split.
apply H. simpl. left. auto. auto.
Qed.      
   

Lemma listInclusion: forall (A: Type) (lst1 lst2 : list A) , uniqList lst1 /\ uniqList lst2  
/\ (incl lst1 lst2 ) -> length (lst2) >= length (lst1).
Proof. intros. destruct H. destruct H0.   assert ((Datatypes.length lst2 >= Datatypes.length lst1)  \/ ~(Datatypes.length lst2 >= Datatypes.length lst1)).
apply excluded_middle. destruct H2. auto. 
apply pigeonhole_principle in H1. rewrite repeatUniq in H1. unfold not in H1. exfalso. apply H1. auto. 
omega.
Qed.     

(*elements in l1 will be filtered out from l2*)
Fixpoint filterList (A:Type) (l1: list A) (l2: list A) (decA: forall (x y:A), {x=y} + {x<>y}) : list A:=
match l2 with
| nil => nil
| e'::lst => if inList decA e' l1 then filterList  l1 lst decA else e'::filterList  l1 lst decA
end. 

(*get elements of l2 also belonging to l1*)
Fixpoint filterListReverse (A:Type) (l1: list A) (l2: list A) (decA: forall (x y:A), {x=y} + {x<>y}) : list A:=
match l2 with
| nil => l1
| e'::lst => if inList decA e' l1 then e'::filterListReverse l1 lst decA else filterListReverse l1 lst decA
end. 

(*merge two lists withtout duplicate jointed elements*)
(*used when l1 and l2 are uniqList*)
Definition mergeList' (A:Type) (l1: list A) (l2: list A) (decA: forall (x y:A), {x=y} + {x<>y})  : list A :=
let l2':= filterList l1 l2 decA in
app l1 l2'.

(*relation between inList and In*)
Lemma inListLemma: forall (A:Type) (l1:list A) (i:A) (decA: forall (x y:A), {x=y} + {x<>y})
, In i l1 -> inList decA i l1 = true.
Proof. intros. induction l1. inversion H. simpl.
destruct  (decA i a). auto. apply IHl1. simpl in H. destruct H. unfold not in n. symmetry in H. exfalso. apply n. auto. auto.
Qed.       

(*relation between inList and In*)
Lemma reverseinListLemma: forall (A:Type) (l1:list A) (i:A) (decA: forall (x y:A), {x=y} + {x<>y})
, inList decA i l1 = true ->  In i l1.
Proof. intros. induction l1. simpl in H.   inversion H. 
simpl in H. 
destruct  (decA i a). rewrite e. simpl. left. auto.
simpl. right. apply IHl1. auto.     
Qed.    

(*aux lemma, if i is in filterList l1 l2, then i is not in l1*)
Lemma filterL1: forall (A:Type)  (l1: list A) (l2: list A) (decA: forall (x y:A), {x=y} + {x<>y}),
forall i, In i (filterList l1 l2 decA)  -> ~ In i l1.
Proof. intros A l1. induction l1.
- intros. simpl in H. unfold not.  intros. inversion H0.
- intros. unfold not.  intros. simpl in H0. destruct H0.
+ induction l2.  simpl in H. inversion H. simpl in H.     
destruct (decA a0 a). apply IHl2. auto. 
induction (inList decA a0 l1). apply IHl2 in H. inversion H. simpl in H. destruct H. rewrite <- H0 in H.
 unfold not in n. apply n. auto.  apply IHl2. auto.   
+ induction l2.  simpl in H. inversion H. simpl in H.     
destruct (decA a0 a). apply IHl2. auto. 
remember (inList decA a0 l1).
destruct b.  
destruct (inList decA a0 l1). apply IHl2 in H. auto. inversion Heqb. 
   
 simpl in H.
 destruct H. Focus 2. apply IHl2 in H. auto.
rewrite H in Heqb.
apply inListLemma with (A:=A) (i:=i) (decA:=decA) (l1:=l1)  in H0. rewrite H0 in Heqb. inversion Heqb.
Qed.       

(*aux lemma, if i is in filterList l1 l2, then i is in l2*)
Lemma filterL2: forall (A:Type)  (l1: list A) (l2: list A) (decA: forall (x y:A), {x=y} + {x<>y}),
forall i, In i (filterList l1 l2 decA)  ->  In i l2.
Proof. intros A l1. induction l1.
- intros. induction l2. simpl in H. inversion H. simpl in H.
destruct H. simpl. left. auto. simpl. right. apply IHl2. auto.   
- intros.  simpl in H. induction l2. simpl in H. inversion H. 
simpl in H. destruct (decA a0 a ). simpl in H. simpl. right. apply IHl2. auto.
  destruct (inList decA a0 l1). simpl. right. apply IHl2. auto. 
simpl in H. destruct H. simpl. left. auto. simpl. right. apply IHl2. auto.         
Qed. 

(*aux lemma, if a is in lst1 and not in lst1, then it is in filterList lst2 lst1 *)
Lemma filterIn: forall (A:Type) (lst1 lst2: list A) (decA : forall x y : A, {x = y} + {x <> y}) 
(a: A),
In a lst1 -> ~In a lst2 ->  In a (filterList (lst2) (lst1) (decA)).
Proof. intro A. intro lst1. induction lst1.
- intros. inversion H.
- intros.  simpl. remember (inList decA a lst2).  destruct (b). 
Check reverseinListLemma. symmetry in Heqb. apply reverseinListLemma in Heqb.   
destruct H. rewrite <- H in H0. exfalso;apply H0;auto. eapply IHlst1. auto. auto. destruct H. simpl. left. auto.
simpl. right. eapply IHlst1. auto. auto.
Qed.       
Print mergeList'.

Lemma inclInvariant : forall (A:Type) (lst1 lst2 : list A) (a:A), incl lst1 lst2 ->  In a lst2 -> 
~In a lst1 -> incl (a::lst1) lst2.
Proof. intros. unfold incl. intros. simpl in H2. destruct H2.  rewrite <- H2. auto. 
unfold incl in H. apply H in H2. auto.      
Qed. 

Lemma uniqIn: forall (A:Type) (l1 l2: list A) (a:A) (decA: forall (x y:A), {x=y}+{x<>y}),  In a (filterList l1 l2 decA) -> In a l2.
Proof. intros A l2. induction l2.
- intros.  induction l2. simpl in H. auto. simpl in H. destruct H. simpl. left. auto.
simpl. right. auto.
-  intros. induction l0. simpl in H. inversion H.
simpl in H. 
 destruct (decA a1 a). apply IHl0 in H. simpl. right. auto.
destruct (inList decA a1 l2).
apply IHl0 in H. right. auto.
simpl in H. destruct H. rewrite H. simpl. left. auto.
apply IHl0 in H. simpl. right. auto.
Qed.          

(*aux lemma*)
Lemma filterInclu: forall (A:Type) (l1 l2 :list A) (decA: forall x y : A, {x = y} + {x <> y}), incl (filterList l2 l1 decA) l1.
Proof. intros. unfold incl. intros.

generalize dependent l2. induction l1.
intros. destruct l2. simpl in H. inversion H. simpl in H. inversion H.
intros. simpl in H.  destruct (inList decA a0 l2).
simpl. right.  apply IHl1 with l2. auto. simpl in H. destruct H. simpl. left. auto.
simpl in H. simpl. right. apply IHl1 with l2. auto.
Qed.                     

(*aux lemma*)
Lemma mergeInclu: forall (A:Type) (l1 l2 l:list A) (decA: forall x y : A, {x = y} + {x <> y}),
 incl l1 l -> incl l2 l -> incl (mergeList' l1 l2 decA) l.
Proof. intros. unfold mergeList'. 
apply incl_app. auto. 
assert (incl (filterList l1 l2 decA) l2).
Focus 2. 
eapply incl_tran. apply H1. apply H0. 
apply filterInclu. 
Qed.  

Lemma  uniqListFilter: forall  (A:Type) (l1 l2:list A) (decA: forall (x y:A), {x=y}+{x<>y}), uniqList l1 -> uniqList l2 -> uniqList (filterList l1 l2 decA).
Proof. intros A l2. 
Check filterL1. 
Print filterList.
induction l2. 
- intros. induction l2. simpl. 
Print uniqList.  apply uniqL_nilL. simpl. 
apply uniqL_push. apply IHl2.   inversion H0. subst. auto.
inversion H0. subst. apply IHl2 in H3. 
unfold not. intros.
apply uniqIn in H1. unfold not in H4. apply H4. auto.
- intros. inversion H. subst. induction l0. simpl. apply uniqL_nilL.
simpl.  
destruct (decA a0 a). apply IHl0.   inversion H0;subst. auto.
destruct (inList decA a0 l2).
    inversion H0;subst. apply IHl0 in H5. auto.
apply uniqL_push. apply IHl0. inversion H0; subst. auto.
unfold not. intros.
apply uniqIn in H1. inversion H0;subst. unfold not in H7. apply H7. auto.        
Qed. 

Lemma uniqMerge: forall (A:Type) (l1 l2:list A) (decA: forall (x y:A), {x=y}+{x<>y}), uniqList l1 -> uniqList l2 -> uniqList (mergeList' l1 l2 decA).
Proof.
intros. unfold mergeList'. 
apply uniqApp'. auto. Focus 2. intros. unfold not. intros.
 Check filterL1. apply filterL1 in H2. unfold not in H2. apply H2. auto.
Focus 2. intros.     apply filterL1 in H1. auto.
  apply uniqListFilter. auto. auto.  
Qed.

Lemma mapPermu: forall (A: Type) (B: Type)  (lst1 lst2: list A) (f: A -> B),
equivList lst1 lst2 ->
equivList (map f lst1) (map f lst2).
Proof. 
intros. apply Permutation_map. auto.
Qed.  

Lemma inListFalse: forall (A:Type) a l decA , (~ In a l) -> @inList A decA a l = false.
Proof. intros.
induction l. simpl. auto. 
simpl. 
destruct (decA a a0). unfold not in H. exfalso. apply H. left;auto. 
apply IHl. unfold not. intros. apply H. right;auto.   
Qed.    

Lemma reverseinListFalse: forall (A:Type) a l decA , @inList A decA a l = false -> (~ In a l).
Proof. intros.
induction l. unfold not. intros. inversion H0. 
unfold not.  intros. simpl in H.   
destruct (decA a a0). inversion H. destruct H0. exfalso;apply n;auto.
apply IHl. auto. auto.
Qed.  

Lemma inListEquiv: forall (A:Type) l1 a  l2 decA,
equivList l1 l2 ->
@inList A decA a l1 = @inList A decA a l2.
Proof. intros A l2. induction l2.
- intros. destruct l2. simpl. auto. 
assert (~(Permutation nil (a0::l2))).
apply Permutation_nil_cons. exfalso. apply H0;auto.   
- intros. destruct l0. unfold equivList in H. 
assert (Permutation nil (a::l2)). 
apply Permutation_sym. auto.       
assert (~(Permutation nil (a::l2))).
apply Permutation_nil_cons. exfalso. apply H1;auto. 
simpl. 
destruct (decA a0 a). 
destruct (decA a0 a1). auto. rewrite <- e in H. 
assert (In a0 (a1::l0)). eapply Permutation_in. 
unfold equivList in H. apply H. left;auto. destruct H0. exfalso;apply n;auto. 
SearchAbout inList.      symmetry. eapply inListLemma. auto.
destruct (decA a0 a1). eapply inListLemma. rewrite <- e in H. 
assert (In a0 (a::l2)). unfold equivList in H.  
assert (Permutation (a0::l0) (a::l2)). 
apply Permutation_sym. auto.          eapply Permutation_in. apply H0. left;auto. 
destruct H0. exfalso;apply n;auto. auto. remember (inList decA a0 l2). 
remember (inList decA a0 l0). destruct b. assert (In a0 l2).
SearchAbout inList. eapply reverseinListLemma.
symmetry. apply Heqb. unfold equivList in H. 
assert (In a0 (a1::l0)).  eapply Permutation_in. apply H. 
right;auto. destruct H1. exfalso;apply n0;auto. rewrite Heqb0. 
SearchAbout inList. 
symmetry;apply inListLemma. auto. symmetry in Heqb. assert (~In a0 l2). eapply reverseinListFalse.
apply Heqb. rewrite Heqb0.  symmetry. apply inListFalse. unfold not;intros. apply H0. 
assert (In a0 (a::l2)).     
eapply Permutation_in. unfold equivList in H. assert (Permutation (a1::l0) (a::l2)). 
  apply Permutation_sym. auto.  apply H2. right;auto. destruct H2. exfalso;apply n;auto. auto.
Qed.   

Lemma filterListEquiv: forall (A:Type) l l1 l2  decA, 
equivList l1 l2 -> 
equivList (@filterList A l1 l decA) (@filterList A l2 l decA).
Proof. intros A l.  induction l. intros. simpl. apply Permutation_refl.
intros.  simpl.  remember (inList decA a l1). destruct b.   

remember (inList decA a l2). destruct b.      
apply IHl.  auto.   assert (( inList decA a l1) = (inList decA a l2)). eapply inListEquiv.
auto.  rewrite <- Heqb in H0. rewrite <- Heqb0 in H0. inversion H0.  
remember (inList decA a l2).  
assert (( inList decA a l1) = (inList decA a l2)). eapply inListEquiv.
auto. rewrite <- Heqb in H0. rewrite <- H0 in Heqb0. rewrite  Heqb0. 
unfold equivList. apply perm_skip. apply IHl. auto.
Qed.                

Lemma filterListEquiv': forall (A:Type) l2' l1'  l1 l2  decA, 
equivList l1 l2 ->
equivList l1' l2' ->
equivList (@filterList A l1 l1' decA) (@filterList A l2 l2' decA).  
Proof. 
intros. generalize dependent l2. generalize dependent l1. 
   induction H0.
- intros. simpl. constructor.
- intros. simpl.        
remember (inList decA x l1).
destruct b. 
remember ( inList decA x l2).
destruct b.  apply IHPermutation. auto. 
assert (In x l1). SearchAbout inList. eapply reverseinListLemma. symmetry. apply Heqb. 
assert (~ In x l2). eapply reverseinListFalse. symmetry. apply Heqb0.  
assert (In x l2). eapply Permutation_in. apply H. auto. exfalso;apply H2;auto.    
remember (inList decA x l2). destruct b. 
assert (In x l2). SearchAbout inList. eapply reverseinListLemma. symmetry. apply Heqb0. 
assert (~ In x l1). eapply reverseinListFalse. symmetry. apply Heqb.           
assert ( In x l1).  eapply Permutation_in. apply Permutation_sym in H.   apply H.  auto. exfalso;apply H2;auto.
constructor. apply IHPermutation. auto.     
- intros. simpl.
  remember (inList decA y l1). 
  destruct b.    
  remember (inList decA x l1).
destruct b. 
  remember (inList decA x l2).
destruct b.
  remember (inList decA y l2).
destruct b.   
apply filterListEquiv. auto. 
assert (In y l1). SearchAbout inList. eapply reverseinListLemma. symmetry. apply Heqb. 
assert (~ In y l2). eapply reverseinListFalse. symmetry. apply Heqb2.  
assert (In y l2). eapply Permutation_in. apply H. auto. exfalso;apply H1;auto.    
remember (inList decA y l2 ). destruct b.   
assert (In x l1). SearchAbout inList. eapply reverseinListLemma. symmetry. apply Heqb0. 
assert (~ In x l2). eapply reverseinListFalse. symmetry. apply Heqb1.  
assert (In x l2). eapply Permutation_in. apply H. auto. exfalso;apply H1;auto.
assert (In x l1). SearchAbout inList. eapply reverseinListLemma. symmetry. apply Heqb0. 
assert (~ In x l2). eapply reverseinListFalse. symmetry. apply Heqb1.  
assert (In x l2). eapply Permutation_in. apply H. auto. exfalso;apply H1;auto.    
 remember (inList decA x l2). destruct b. 
remember (inList decA y l2 ). destruct b. 
 assert (In x l2). SearchAbout inList. eapply reverseinListLemma. symmetry. apply Heqb1. 
assert (~ In x l1). eapply reverseinListFalse. symmetry. apply Heqb0.  
assert (In x l1). eapply Permutation_in. apply Permutation_sym in H.  apply H. auto. exfalso;apply H1;auto.
 assert (In x l2). SearchAbout inList. eapply reverseinListLemma. symmetry. apply Heqb1. 
assert (~ In x l1). eapply reverseinListFalse. symmetry. apply Heqb0.  
assert (In x l1). eapply Permutation_in. apply Permutation_sym in H.  apply H. auto. exfalso;apply H1;auto.  
remember (inList decA y l2).
destruct b. 
apply perm_skip.  apply filterListEquiv.
auto.
assert (In y l1). SearchAbout inList. eapply reverseinListLemma. symmetry. apply Heqb. 
assert (~ In y l2). eapply reverseinListFalse. symmetry. apply Heqb2.  
assert (In y l2). eapply Permutation_in. apply H. auto. exfalso;apply H1;auto.      
remember (inList decA x l1).
destruct b.   
remember (inList decA x l2). destruct b.
remember (inList decA y l2). destruct b.
assert (In y l2). SearchAbout inList. eapply reverseinListLemma. symmetry. apply Heqb2. 
assert (~ In y l1). eapply reverseinListFalse. symmetry. apply Heqb.  
assert (In y l1). eapply Permutation_in. apply Permutation_sym in H.  apply H. auto. exfalso;apply H1;auto.
      
  
apply perm_skip.  apply filterListEquiv. 
auto. 
remember ( inList decA y l2 ). destruct b. 
assert (In y l2). SearchAbout inList. eapply reverseinListLemma. symmetry. apply Heqb2. 
assert (~ In y l1). eapply reverseinListFalse. symmetry. apply Heqb.  
assert (In y l1). eapply Permutation_in. apply Permutation_sym in H.  apply H. auto. exfalso;apply H1;auto.
assert (In x l1). SearchAbout inList. eapply reverseinListLemma. symmetry. apply Heqb0. 
assert (~ In x l2). eapply reverseinListFalse. symmetry. apply Heqb1.  
assert (In x l2). eapply Permutation_in. apply H. auto. exfalso;apply H1;auto.    
remember (inList decA x l2). destruct b.
remember (inList decA y l2). destruct b. 
 assert (~ In x l1). eapply reverseinListFalse. symmetry. apply Heqb0.  
assert (In x l2). eapply reverseinListLemma. symmetry. apply Heqb1. 
assert (In x l1). eapply Permutation_in. apply Permutation_sym in H.  apply H. auto. exfalso;apply H0;auto.
 assert (~ In x l1). eapply reverseinListFalse. symmetry. apply Heqb0.  
assert (In x l2). eapply reverseinListLemma. symmetry. apply Heqb1. 
assert (In x l1). eapply Permutation_in. apply Permutation_sym in H.  apply H. auto. exfalso;apply H0;auto.
remember (inList decA y l2). destruct b. 
assert (In y l2). SearchAbout inList. eapply reverseinListLemma. symmetry. apply Heqb2. 
assert (~ In y l1). eapply reverseinListFalse. symmetry. apply Heqb.  
assert (In y l1). eapply Permutation_in. apply Permutation_sym in H.  apply H. auto. exfalso;apply H1;auto.  
assert (app (app (y::nil) (x::nil)) (filterList l1 l decA) =  (y :: x:: filterList l1 l decA)).
auto. rewrite <- H0. 
assert (app (app (x::nil) (y::nil)) (filterList l2 l decA) =  (x :: y:: filterList l2 l decA)).
auto. rewrite <- H1.  
 apply Permutation_app. simpl.    apply perm_swap. 
apply filterListEquiv. auto.
- intros. remember H. clear Heqe.
apply IHPermutation1 in e.
remember H. clear Heqe0.   
apply IHPermutation2 in H.
assert  (equivList  (filterList l2 l' decA) (filterList l1 l' decA)).
apply filterListEquiv. apply Permutation_sym. auto.    
assert (equivList (filterList l1 l decA) (filterList l1 l' decA)).
eapply perm_trans. apply e. apply H0. 
eapply perm_trans. apply H1. auto.   
Qed.     


Lemma filterEquiv: forall (A:Type) f l1 l2,
equivList l1 l2 ->
equivList (@filter A f l1) (@filter A  f l2).
Proof. intros. induction H.
- intros. simpl. constructor.
- simpl.   
destruct (f x).
apply perm_skip. auto.
auto.
- simpl. destruct (f y). destruct (f x). apply perm_swap. 
constructor. apply Permutation_refl.
destruct (f x). apply Permutation_refl.
apply Permutation_refl.
- eapply perm_trans. apply IHPermutation1. apply IHPermutation2.
Qed.    

(*aux funtion, generate value from the evaluation of the expression*)
Fixpoint calculateExpr (en:value_env) (exp: expr) : option range_typ :=
match evalMonad en exp with
| Error s => None
| Result (AInt i) => Some (inl (inl (inl i)))
| Result (AFloat q) => Some (inl (inl (inr q)))
| Result (AString s) => Some (inl (inr s))
| _ => None 
end.


Fixpoint calculateExprList (en:value_env) (lst: list expr): (ErrorOrResult) :=
match lst with
| nil => Result (nil)
| ex::lst' => match calculateExpr en ex with
                  | None =>  (Error error2)
                  | Some v => match calculateExprList en lst' with
                                      | (Error s) => (Error s)
                                      | Result (vlst) => Result (v:: vlst)
                                      end
                  end
end.
