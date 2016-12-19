(*AST of SMEDL*)
(*Syntax related to the monitor is defined in this file, which will be used in definition of semantics*)
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
  Coq.Classes.EquivDec.

Require Import Coq.Sorting.Permutation.

 
Set Implicit Arguments.
Set Decidable Equality Schemes
(*Set Boolean Equality Schemes.*)
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Require Import Coq.Strings.Ascii.

Open Scope N_scope.

Definition typeErr : string := "Type error".
Definition zeroErr: string := "zero divisor". 


(*Used to distinct between normal value and error*)
Inductive ErrorOrResult{T} :=
| Result : forall v: T, @ErrorOrResult T
| Error : forall s: string, @ErrorOrResult T.


Section AST.

(* type            = ?/[a-zA-Z][A-Za-z0-9_]*/? ;
   identifier      = ?/[a-zA-Z][A-Za-z0-9_]*/? ;
   identifier_list = @:identifier {',' @:identifier}* | () ;
   target          = identifier  ;
   integer         = ?/[-+]?[0-9]+/? ;
   float           = ?/[-+]?[0-9]*\.?[0-9]+/? ; *)

(*supported type in SMEDL*)
Inductive typ :=
| Int 
| Float
| Str
| Pointer
| Opaque
| Thread
.

Scheme Equality for typ.


(* variable_declaration
       = type:type var:identifier {',' var:identifier}* ';' ; *)

(* atom = integer | float | identifier | 'true' | 'false' | string | 'null' ; *)

Inductive atom : Set :=
  | AInt   : Z -> atom
  | AFloat : Q -> atom
  | AIdent : string -> atom
  | ABool  : bool -> atom
  | ANull  : atom
  | AString : string -> atom.

   Scheme Equality for atom.
Check atom_eq_dec. 

(*typing environment*)
Definition typ_env := (list (atom * typ)).

(*supported value in SMEDL*)
(*Z and nat has different usage, but nat may be removed later*)
Definition range_typ : Set := (Z+Q+string+nat).

Definition range_typ_dec (re:range_typ):  forall re', {re = re'} + {re <> re'}.
Proof. repeat decide equality.   Qed.  

Check range_typ_dec. 
(*value environment*)
(*used to represent the scope in SMEDL*)
Definition value_env := (list (atom *( typ * range_typ))).

(*return domination*)
Definition dom (A:Type) (B: Type) (env: list (A*B)): list A := 
map (fun v:(A*B) => fst v) env.

Definition string_dec_bool (s1:string) (s2:string) : bool :=
if string_dec s1 s2 then true else false. 

(*currently not used*)
Inductive uniq (A : Type) : list (atom * A) -> Prop :=
|  uniq_nil : uniq nil
| uniq_push : forall (x : atom) 
                  (a : A) (E : list (atom * A)),
                uniq E ->
                ~(In x (dom E)) -> uniq ((x,a)::E).

Inductive uniqList (A : Type) : list (A) -> Prop :=
|  uniqL_nilL: uniqList nil
| uniqL_push : forall  
                  (a : A) (E : list ( A)),
                uniqList E ->
                ~(In a (E)) -> uniqList ((a)::E).

Lemma uniqListNoDupEq: forall (A:Type) l,  uniqList l <-> @NoDup A l.
Proof. intros.
split.
- induction l. intros. constructor.
 intros. inversion H. subst. apply NoDup_cons;auto.
- induction l. intros. constructor. intros. inversion H;subst. apply uniqL_push;auto.
Qed.

                    
(*auxiliary lemma*)
(*append of two jointed unique list is a uniqlist*)
Lemma uniqApp': forall (A:Type) (l1 l2:list A),
uniqList l1 -> uniqList l2 -> (forall i, In i l1 -> ~(In i l2)) ->
(forall i, In i l2 -> ~(In i l1)) -> uniqList(l1 ++ l2).  
Proof. intros A l1.
induction l1. intros. simpl. auto.   
intros. inversion H. subst.
assert (~ In a l2). apply H1. simpl. left. auto.    
simpl. apply uniqL_push. apply IHl1. auto. auto. intros. apply H1. simpl. right. auto.
intros. apply H2 in H4. unfold not in H4. unfold not. intros. apply H4.
simpl. right. auto. unfold not. intros.
apply in_app_iff in H4. destruct H4. 
unfold not in H6. apply H6. auto. unfold not in H3. apply H3. auto.
Qed.       
       
                  
(*auxiliary function, bool version of "In" *)
Fixpoint inList (A: Type) (decA: forall (x y:A), {x=y} + {x<>y}) (x: A) (lst : list A) : bool :=
match lst with
| nil => false
| y::lst' => if decA x y then true else (inList decA x lst')
end.


(*two lists are permutation of each other*)
Definition equivList {A: Type}   (l1: list A) (l2: list A) : Prop := 
Permutation l1 l2.

(*auxiliary function, update value of a varialbe in the environment*)
Fixpoint updateValueEnv (a: atom) (t: typ) (v: option range_typ) (en:value_env): value_env  :=
match v with
| None => en
| Some v' => 
match a with
| AIdent i => match en with
                        | nil => (a,(t,v'))::nil
                        | (a',(t',v''))::en' => if  atom_eq_dec a a' then
                                                           if typ_eq_dec  t t' then (a',(t',v'))::(updateValueEnv a t (Some v') en') 
                                                                    else 
                                                                    (a',(t',v'')) :: (updateValueEnv a t (Some v') en')
                                                     else
                                                              (a',(t',v'')) :: (updateValueEnv a t (Some v') en')
                   end

| _ => en
end
end.

(*auxiliary function, create a new environment based on the variable names, types and values*)
Fixpoint createValueEnv (nlst: list string) (tlst: list typ) (vlst: list range_typ): (ErrorOrResult):=
match nlst,tlst,vlst with
| s::nlst', t::tlst', v::vlst' => match createValueEnv nlst' tlst' vlst' with
                                                       | Error (s) => (Error s)
                                                       | Result (ve) => Result ((AIdent s,(t,v)):: ve)
                                                    end
| _, _, _ => Error ("number of list not matched")
end. 

(*auxiliary function,get the type of a variable from the environment*)
Fixpoint getType (a: atom) (en:typ_env) : option typ :=
match a with
| AIdent i => match en with
                        | nil => None
                        | (a',v)::en' => if  atom_eq_dec a a' then Some v else getType a en'
                   end
| _ => None
end.

(*auxiliary function,get the value of a variable from the environment*)
Fixpoint getValue (a: atom) (en:value_env) : option range_typ :=
match a with
| AIdent i => match en with
                        | nil => None
                        | (a',(_,v))::en' => if  atom_eq_dec a a' then Some v else getValue a en'
                   end
| _ => None
end.


(*extend environment*)
(*assume that newly added variables are fresh to the environment*)
Definition extendEnv (A:Type) (en: list (atom * A)) (pen: list (atom * A)) : list (atom * A) := app en pen.

(*check if the value is consistent with the type*)
(*not used for now*)
Definition typeCheck (prod: (atom *( typ * range_typ))) : Prop:=
(exists v', (fst (snd prod)) =Int /\ (snd (snd prod)) = inl (inl (inl v')))
\/ (exists v', (fst (snd prod)) =Float /\ (snd (snd prod)) = inl (inl (inr v')))
\/ (exists v', (fst (snd prod)) =Str /\ (snd (snd prod)) = inl (inr v'))
\/ (exists v', (fst (snd prod)) =Pointer /\ (snd (snd prod)) = inr v')
\/  (exists v', (fst (snd prod)) =Thread /\ (snd (snd prod)) = inr v')
\/  (exists v', (fst (snd prod)) =Opaque /\ (snd (snd prod)) = inr v').

(* expression = or_ex:and_expr {'||' or_ex:and_expr}+ | @:and_expr ;
   expression_list = @:expression {',' @:expression}* | () ;
   and_expr = and_ex:sub_expr {'&&' and_ex:sub_expr}+ | @:sub_expr ;
   sub_expr = {'!!'}*'!(' not_ex:expression ')'
            | {'!!'}*'(' @:expression ')'
            | @:comp_expr ;
   comp_expr = comp:arith_expr
                 {operator:('>=' | '<=' | '==' | '!=' | '>' | '<')
                      comp:arith_expr}+
             | '(' @:comp_expr ')'
             | @:arith_expr ;
   arith_expr = arith:term {operator:('+' | '-' | '*' | '/' | '%') arith:term}+
              | @:term ;
   term = {unary:('+' | '-' | '~' | '!')}* atom:atom {trailer:trailer}*
        | {unary:('+' | '-' | '~')}* '(' @:arith_expr ')' ;
   trailer = '[' [index:expression] ']'
           | '(' [params:expression_list] ')'
           | '.' dot:identifier {trailer:trailer}* ; *)

Inductive expr : Set :=
  (* or_expr *)
  | EOr : expr -> expr -> expr

  (* and_expr *)
  | EAnd : expr -> expr -> expr

  (* sub_expr *)
  (* | ESubNot : nat -> expr -> expr *)
  (* | ESub : nat -> expr -> expr *)

  (* comp_expr *)
  | EEq  : expr -> expr -> expr
  | ENeq : expr -> expr -> expr
  | ELt  : expr -> expr -> expr
  | ELe  : expr -> expr -> expr
  | EGt  : expr -> expr -> expr
  | EGe  : expr -> expr -> expr

  (* arith_expr *)
  | EPlus  : expr -> expr -> expr
  | EMinus : expr -> expr -> expr
  | EMult  : expr -> expr -> expr
  | EDiv   : expr -> expr -> expr
  | EMod   : expr -> expr -> expr

  (* term *)
  | EPos : expr -> expr
  | ENeg : expr -> expr
(*  | ECmp : expr -> expr*)
  | ENot : expr -> expr

  | EAtom  : atom -> expr

     (* TODO *)
  | EIdx : atom -> N -> expr

  | EApp : atom -> list expr -> expr

    (* TODO *)
  | EDot : expr -> expr -> expr.

SearchAbout list sumbool.



(* event_definition =
       error:['error'] event_id:identifier ['(' params:parameter_list ')']
           ['=' definition:expression] ;
   parameter_list = @:type {',' @:type}* | () ;
   event_definition_list = @:event_definition {',' @:event_definition}* ';' ; *)


 Lemma expr_eq_dec : forall e1 e2: expr, {e1 = e2} + {e1 <> e2}.
Proof.
 fix rec 1.
 repeat decide equality.
Qed.

(*Instance expr_eq_dec1: EqDec expr eq. *)


Record exprlist :={
lst: list expr
}.

Lemma exprlist_eq_dec :
 forall e1 e2: exprlist, {e1 = e2} + {e1 <> e2}.
Proof. pose proof expr_eq_dec. repeat decide equality.  
Qed. 


Inductive EventKind := Internal | Imported | Exported.

Definition eventKind_dec (n m : EventKind) : {n = m} + { n <> m}.
Proof. repeat decide equality. 
Qed. 

Record event_definition : Set := {
  eventKind   : EventKind;
  eventError  : bool;
  eventId     : string;
  eventParams : list typ;
 (* eventParams : list string;*)
  (*eventDef    : option expr*)
}.


Definition event_definition_dec (n m : event_definition) : {n = m} + { n <> m}.
Proof. repeat decide equality. 
Qed. 

Record correct_event_definition (ev : event_definition) : Prop := {
}.

(* actions = '{' actions:action_item_list '}' ;
   action_item_list = @:action_item ';' { @:action_item ';' }* ;
   action_item
       = state_update:state_update
       | raise_stmt:raise_stmt
       | instantiation:instantiation_stmt
       | call_stmt:call_stmt ;
   raise_stmt = 'raise' id:identifier ['(' expr_list+:expression_list ')'] ;
   instantiation_stmt
       = 'new' id:identifier ['(' state_update_list+:state_update_list ')'] ;
   call_stmt = target:target '(' expr_list+:expression_list ')' ;

   state_update = target:target operator:('++' | '--')
       | target:target operator:'=' expression:expression ;
   state_update_list = @:state_update {',' @:state_update}* | () ; *)

Inductive state_update : Set :=
 (* | SUIncrement : expr -> state_update
  | SUDecrement : expr -> state_update*)
  | SUAssign : expr -> expr -> state_update.

Lemma state_update_eq_dec :
 forall e1 e2: state_update, {e1 = e2} + {e1 <> e2}.
Proof. intros. decide equality. apply expr_eq_dec. 
apply expr_eq_dec.
Qed.   

(*Instantiation and CallStmt are not used for now*)
Inductive action : Set :=
  | StateUpdate : state_update -> action
  | RaiseStmt (ident : string) (exprs : list expr) : action
  | Instantiation (ident : string) (updates : list state_update) : action
  | CallStmt (target : string) (args : list expr) : action.



Lemma action_eq_dec :
 forall e1 e2: action, {e1 = e2} + {e1 <> e2}.
Proof. intros. pose proof  state_update_eq_dec. 
pose proof expr_eq_dec.
repeat decide equality.
Qed.  


(* event_instance = expression:expression ['when' when:expression] ; *)

Record event_instance : Set := {
  event: event_definition; (*event definition of this instance*)
  eventArgs     : list string; (*indentifiers*)
  eventWhenExpr : option expr
}.



Definition event_instance_dec (n m : event_instance) : {n = m} + { n <> m}.
Proof.  intros. decide equality. Focus 3.
apply event_definition_dec. 
Focus 2.  
repeat decide equality.
 decide equality.
apply expr_eq_dec.                 
Qed. 

Check string_dec. 

(* step_definition = step_event:event_instance [step_actions:actions] ; *)

Definition scenario_state := string. 



Record step : Set := {
  pre_state : scenario_state; (*source state of the step*)
  stepEvent : event_instance;
  stepActions : list action;
  pro_state : scenario_state (*target state of the step*)
}.

Definition step_dec (n m : step) : {n = m} + { n <> m}.
Proof.  pose proof action_eq_dec. pose proof expr_eq_dec.
 repeat decide equality.
Qed.  




(* trace_definition
       = start_state:identifier '->'
           {trace_steps+:step_definition '->'}+  end_state:identifier
           ['else' [else_actions:actions] '->' else_state:identifier] ; *)

Record trace : Set := {
  startState  : string;
  traceSteps  : list step;      (* non-empty *)
  endState    : string;
  elseActions : list action;
  elseState   : option string
}.

Definition trace_dec (n m : trace) : {n = m} + { n <> m}.
Proof.  pose proof expr_eq_dec.
 repeat decide equality. Qed. 

Record correct_trace (tr : trace) : Prop := {
  _ : (0 < length (traceSteps tr))%nat
}.

(* scenario_definition
       = atomic:['atomic'] scenario_id:identifier
           ':' traces:{trace_definition}+ ; *)

(*state machine*)
Record scenario : Set := {
  isAtomic   : bool;
  scenarioId : string;
  traces     : list trace       (* non-empty *);
  alphabet : list event_definition (*list of events triggering the transition in the scenario*)
}.

Definition scenario_dec (n m : scenario) : {n = m} + { n <> m}.
Proof. pose proof expr_eq_dec.
 repeat decide equality. Qed. 

Record correct_scenario (s : scenario) : Prop := {
  _ : List.Forall correct_trace (traces s);
  _ : (0 < length (traces s))%nat
}.

(*mapping from scenario to its current state*)
(*assume that with in the same monitor, all states in different state machine have a unique name*)
Definition scenario_env := (list (scenario*scenario_state)).

Definition scenario_state_dec (n m : scenario*scenario_state) : {n = m} + { n <> m}.
Proof. pose proof scenario_dec. pose proof string_dec. 
 repeat decide equality. Qed. 

Print string_dec. 
Fixpoint getScenarioState (sce:scenario) (env: scenario_env) : option  scenario_state :=
match env with
| nil => None
| (s,e)::en' => if (string_dec) (scenarioId sce) (scenarioId s) then Some e else getScenarioState sce en'
end.


Fixpoint updateScenarioState' (sce:scenario) (st:scenario_state) (env:scenario_env) :  scenario_env :=
match env with
| nil => nil
| (s,e)::en' => if string_dec (scenarioId s) (scenarioId sce) then (s,st)::updateScenarioState' sce st en' else (s,e)::updateScenarioState' sce st en'
end.

(* import_definition = '#import' import_id:identifier ;
   object =
       imports+:{import_definition}*
       'object' object:identifier
       ['identity' identity+:{variable_declaration}+]
       ['state' state+:{variable_declaration}+]
       'events'
           { 'internal' internal_events+:event_definition_list
           | 'exported' exported_events+:event_definition_list}*
           'imported' imported_events+:event_definition_list
           { 'imported' imported_events+:event_definition_list
           | 'internal' internal_events+:event_definition_list
           | 'exported' exported_events+event_definition_list}*
       'scenarios'
           scenarios+:{scenario_definition}+ $ ; *)

(*monitor*)
Record object : Type := {
  imports    : list string;
  objectId   : string;
  identities : typ_env;      (* name -> type *)
  variables  : typ_env;      (* name -> type *)
  events     : list event_definition;
  scenarios  : list scenario          (* non-empty *)
}.

Definition object_dec (n m : object) : {n = m} + { n <> m}.
Proof. pose proof expr_eq_dec.
 repeat decide equality. Qed. 


(*check if the event is an imported event*)
Definition importedEvent (ev : event_definition) : Prop :=
  match eventKind ev with
  | Imported => True
  | Internal => False
  | Exported => False
  end.

(*check if the event is an imported or internal event*)
Definition importedOrInternalEvent (ev : event_definition) : Prop :=
 (match eventKind ev with
  | Imported => True
  | Internal => True
  | Exported => False
  end).

Record correct_object (obj : object) : Prop := {
  _ : List.Forall correct_event_definition (events obj);
  _ : List.Exists importedEvent (events obj);
  _ : List.Forall correct_scenario (scenarios obj);
  _ : (0 < length (scenarios obj))%nat
}.

End AST.

Arguments AInt _.
Arguments AFloat _.
Arguments ABool _.
Arguments AIdent _.
Arguments ANull.

Arguments EOr _ _.
Arguments EAnd _ _.

Arguments EEq _ _.
Arguments ENeq _ _.

Arguments ELt _ _.
Arguments ELe _ _.
Arguments EGt _ _.
Arguments EGe _ _.

Arguments EPlus _ _.
Arguments EMinus _ _.
Arguments EMult _ _.
Arguments EDiv _ _.
Arguments EMod _ _.

Arguments EPos _.
Arguments ENeg _.
(* Arguments ECmp _. *)
Arguments ENot _.

Arguments EAtom _.
Arguments EIdx _ _.
Arguments EApp _ _.
Arguments EDot _ _.

Arguments expr.

Section Monad.


(*aux function for evaluation*)
Definition Bind {T} : @ErrorOrResult T -> (T -> @ErrorOrResult T) -> @ErrorOrResult T :=
  fun val func =>
    match val with
    | Error err => Error err
    | Result v => (func v)
    end.

Notation ret v := (Result v).

Notation "x <- m ; y" := (Bind m (fun x => y))
                           (at level 51, right associativity,
                            format "'[v' x  <-  m ; '/' y ']'").

Definition BindZ : ErrorOrResult -> (Z -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <- val;
    match v with
    | AInt n => func n
    | _ => Error typeErr 
    end.

Definition BindQ : ErrorOrResult -> (Q -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <- val;
    match v with
    | AFloat q => func q
    | _  => Error typeErr
    end.

Definition BindNum : ErrorOrResult -> (Z+Q -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <- val;
    match v with
    | AFloat q => func (inr q)
    | AInt n => func (inl n)
    | _  => Error typeErr
    end.

Definition BindBool : ErrorOrResult -> (bool -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <- val;
    match v with
    | ABool b => func b
    | _  => Error typeErr
    end.


Definition BindStr : ErrorOrResult -> (string -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <- val;
    match v with
    | AString s => func s
    | _  => Error typeErr
    end.

Definition BindData: ErrorOrResult -> (Z+Q+bool+string -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <- val;
    match v with
    | AString s => func (inr s)
    | ABool b => func (inl (inr b))
    | AInt n => func (inl (inl (inl n)))
    | AFloat q => func (inl (inl (inr q)))
    | _  => Error typeErr
    end.


Definition BindNumNotZero: ErrorOrResult -> (Z+Q -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <- val;
    match v with
    | AInt n => match n with
                      | Z0 =>  Error zeroErr
                      | _ => func (inl n)
                      end
    | AFloat q => match q with 
                          | (0#1) =>  Error zeroErr
                          | _ => func  (inr q)
                          end
    | _  => Error typeErr
    end.


End Monad.

Notation "x <z- m ; y" := (BindZ m (fun x => y))
                             (at level 51, right associativity,
                              format "'[v' x  <z-  m ; '/' y ']'").

Notation "x <q- m ; y" := (BindQ m (fun x => y))
                             (at level 51, right associativity,
                              format "'[v' x  <q-  m ; '/' y ']'").

Notation "x <num- m ; y" := (BindNum m (fun x => y))
                             (at level 51, right associativity,
                              format "'[v' x  <num-  m ; '/' y ']'").

Notation "x <numn0- m ; y" := (BindNumNotZero m (fun x => y))
                             (at level 51, right associativity,
                              format "'[v' x  <numn0-  m ; '/' y ']'").


Notation "x <bool- m ; y" := (BindBool m (fun x => y))
                              (at level 51, right associativity,
                               format "'[v' x  <bool-  m ; '/' y ']'").

Notation "x <data- m ; y" := (BindData m (fun x => y))
                              (at level 51, right associativity,
                               format "'[v' x  <data-  m ; '/' y ']'").

Notation retInt v := (Result (AInt v)).
Notation retBool v := (Result (ABool v)).
Notation retFloat v := (Result (AFloat v)).
Notation retStr v := (Result (AString v)).


Section Denotation.

Definition Expr := expr.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.


(*expr evaluation*)
(*use monad to hide error info*)
Fixpoint evalMonad (env:value_env) (e:expr): ErrorOrResult :=
match e with
|EOr x y => b1 <bool- (evalMonad env x);
                   b2 <bool- evalMonad env y; 
                   retBool ((b1 || b2))
|EAnd x y => b1 <bool- evalMonad env x;
                   b2 <bool- evalMonad env y;
                   retBool ((b1 && b2))
| ENot x => b1 <bool- evalMonad env x;
                   retBool ( (negb b1))
| EEq x y => n1 <data- evalMonad env x;
                    n2 <data- evalMonad env y;
                    match n1, n2 with
                    | (inl (inl (inl i))), (inl (inl (inl j))) => retBool ( (i =? j))
                    | (inl (inl (inl i))), (inl (inl (inr q))) => retBool ( (Qeq_bool (inject_Z i) q))
                    | (inl (inl (inr p))),(inl (inl (inl j))) => retBool ( (Qeq_bool p (inject_Z j)))
                    | (inl (inl (inr p))),(inl (inl (inr q))) =>  retBool ( (Qeq_bool p q))
                    |  (inl (inr b1)),  (inl (inr b2)) => retBool ( (eqb b1 b2))
                    | (inr s1), (inr s2) => retBool (string_dec_bool s1 s2)
                    | _, _  => Error typeErr
                   end
| ENeq x y => n1 <data- evalMonad env x;
                    n2 <data- evalMonad env y;
                    match n1, n2 with
                    | (inl (inl (inl i))), (inl (inl (inl j))) => retBool ( negb (i =? j))
                    | (inl (inl (inl i))), (inl (inl (inr q))) => retBool ( negb (Qeq_bool (inject_Z i) q))
                    | (inl (inl (inr p))),(inl (inl (inl j))) => retBool ( negb (Qeq_bool p (inject_Z j)))
                    | (inl (inl (inr p))),(inl (inl (inr q))) =>  retBool (negb (Qeq_bool p q))
                    |  (inl (inr b1)),  (inl (inr b2)) => retBool ( negb (eqb b1 b2))
                    | (inr s1), (inr s2) => retBool (negb (string_dec_bool s1 s2))
                    | _, _  => Error typeErr
                   end
| ELt x y => n1 <num- evalMonad env x;
                    n2 <num- evalMonad env y;
                    match n1, n2 with
                    | (inl i), (inl j) => retBool (  (i <? j))
                    |  (inl i), (inr q)=> retBool (  (Qle_bool (inject_Z i) q) && (negb (Qeq_bool (inject_Z i) q)))
                    | (inr p), (inl j) => retBool (  (Qle_bool p (inject_Z j) && negb (Qeq_bool p (inject_Z j))))
                    | (inr p), (inr q) =>  retBool ( (Qle_bool p q) && (negb (Qeq_bool p q)))
                   end

| ELe x y => n1 <num- evalMonad env x;
                    n2 <num- evalMonad env y;
                    match n1, n2 with
                    | (inl i), (inl j) => retBool (  (i <? j))
                    |  (inl i), (inr q) => retBool (  (Qle_bool (inject_Z i) q) )
                    | (inr p), (inl j) => retBool (  (Qle_bool p (inject_Z j) ))
                    | (inr p), (inr q) =>  retBool ( (Qle_bool p q) )
                   end

| EGt x y =>  n1 <num- evalMonad env x;
                    n2 <num- evalMonad env y;
                    match n1, n2 with
                    | (inl i), (inl j)  => retBool (  (i >? j))
                    |  (inl i), (inr q) => retBool (negb (Qle_bool (inject_Z i) q) )
                    | (inr p), (inl j) => retBool ( negb (Qle_bool p (inject_Z j) ))
                    | (inr p), (inr q) =>  retBool (negb (Qle_bool p q) )
                   end
| EGe x y => n1 <num- evalMonad env x;
                    n2 <num- evalMonad env y;
                    match n1, n2 with
                    | (inl i), (inl j)  => retBool ( negb  (i <? j))
                    |  (inl i), (inr q) => retBool ( negb( (Qle_bool (inject_Z i) q) && (negb (Qeq_bool (inject_Z i) q))))
                    | (inr p), (inl j) => retBool ( negb(  (Qle_bool p (inject_Z j) && negb (Qeq_bool p (inject_Z j)))))
                    | (inr p), (inr q) =>  retBool ( negb( (Qle_bool p q) && (negb (Qeq_bool p q))))
                   end

| EPlus x y => n1 <num- evalMonad env x;
                    n2 <num- evalMonad env y;
                    match n1, n2 with
                    | (inl i), (inl j)  => retInt (i+j)
                    |  (inl i), (inr q) => retFloat ((inject_Z i + q))
                    | (inr p), (inl j) => retFloat ((p + inject_Z j))
                    | (inr p), (inr q) =>  retFloat (p + q)
                   end 

| EMinus x y => n1 <num- evalMonad env x;
                    n2 <num- evalMonad env y;
                    match n1, n2 with
                    | (inl i), (inl j)  => retInt (i-j)
                    |  (inl i), (inr q) => retFloat ((inject_Z i - q))
                    | (inr p), (inl j) => retFloat ((p - inject_Z j))
                    | (inr p), (inr q) =>  retFloat (p - q)
                   end 

| EMult x y => n1 <num- evalMonad env x;
                    n2 <num- evalMonad env y;
                    match n1, n2 with
                    | (inl i), (inl j)  => retInt (i*j)
                    |  (inl i), (inr q) => retFloat ((inject_Z i * q))
                    | (inr p), (inl j) => retFloat ((p * inject_Z j))
                    | (inr p), (inr q) =>  retFloat (p * q)
                   end 

| EDiv x y => n1 <num- evalMonad env x;
                    n2 <numn0- evalMonad env y;
                    match n1, n2 with
                    | (inl i), (inl j)  => retInt (i*j)
                    |  (inl i), (inr q) => retFloat ((inject_Z i * q))
                    | (inr p), (inl j) => retFloat ((p * inject_Z j))
                    | (inr p), (inr q) =>  retFloat (p * q)
                   end 

| EMod x y => n1 <z- evalMonad env x;
                    n2 <z- evalMonad env y;
                    retInt (n1 mod n2)

| EPos x => n1 <num- evalMonad env x;
                    match n1 with
                    | inl (n) => retInt (Z.abs n)
                    | inr (q) => retFloat (Qabs q)
                    end

| ENeg x => n1 <num- evalMonad env x;
                    match n1 with
                    | inl (n) => retInt (-n)
                    | inr (q) => retFloat (-q)
                    end

|EAtom x => match x with
    | AIdent i => match getValue  (AIdent i) env with
                        | None => Error typeErr
                        |  Some (inl (inl (inl z))) => retInt (z)
                        | Some (inl (inl (inr q))) => retFloat (q)
                        | Some (inl (inr s)) => retStr (s)
                        | _ => Error typeErr
                        end
    | AInt z => retInt (z)
    | AFloat q =>  retFloat (q)
    | AString s => retStr (s)
    | ANull => retInt (0)
    | ABool b => if b then retInt (1) else retInt (0)
    end
           
| _ => Error typeErr
end.

End Denotation.
