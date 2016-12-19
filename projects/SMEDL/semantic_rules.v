(*definition of semantic rules*)
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

Set Implicit Arguments.
Set Boolean Equality Schemes.

Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Require Import Coq.Strings.Ascii.



(*from state of the state machine and the event instance, get the current step*)
Definition stepStateMap := (scenario_state*event_instance)->option step.
(*construct stepStateMap*)
Definition update_stepStateMap (map: stepStateMap) (key: scenario_state*event_instance) (value: option step): stepStateMap :=
fun (key':scenario_state*event_instance) => if string_dec (fst key') (fst key) 
                                                                          then if event_instance_dec (snd key') (snd key) 
                                                                                     then value 
                                                                                  else map key' 
                                                                       else map key'.


(*given scenario state and event definition, return corresponding list of event_instances*)
Definition transitionEventMap := (option scenario_state* option event_definition) -> list event_instance.
(*construct transtionCondtionMap*)
Definition update_transitionEventMap (map:transitionEventMap) (key:option scenario_state* option event_definition) (value: event_instance) : transitionEventMap :=
fun (key': option scenario_state*option event_definition) => 
match fst key', snd key', fst key, snd key with
| Some fk',Some sk', Some fk,Some sk => if string_dec (fk') (fk) 
                                 then if  string_dec (eventId (sk)) (eventId (sk')) 
                                                  then value::(map key) 
                                          else map key'
                         else map key'
| _,_,_,_ =>map key'
end.

(*map from state to its possible triggering event*)
Definition stateEventDefMap := option scenario_state -> list event_definition.
Definition update_stateEventDefMap (map:stateEventDefMap) (key:option scenario_state) (ev: event_definition) : stateEventDefMap :=
fun (key': option scenario_state) => match key' with
                                                        | None => nil
                                                        | Some s => match key with
                                                                            | None => nil
                                                                            | Some s' => if string_dec s s' then ev::(map (key')) else map key'
                                                                            end
                                                        end
.

(*environment*)
(*scenario_state -> list event_definition*)
Parameter stEvMap: stateEventDefMap.
(*scenario_state*event_definition -> list event_instance*)
Parameter transEvMap : transitionEventMap.
(*scenario_state*event_instance -> option step*)
Parameter stpStMap: stepStateMap. 
Parameter eventList : list event_definition.

 
(*data structure*)

(*used in configuration*)
(*data structure to represent the event raised*)
(*pathE*)
Record raisedEvent : Type :={
  eventDefinition: event_definition;
  eventArguments     : list (range_typ);
  pathEvents : list event_definition (*event tag list*)
}.

Definition raisedEvent_dec (n m : raisedEvent) : {n = m} + { n <> m}.
Proof. repeat decide equality. 
Qed. 


Record updatedVariable: Type :={
  up_var: atom; (*variable *)
  eventTag: event_definition
}.

Definition updatedVariable_dec (n m : updatedVariable) : {n = m} + { n <> m}.
Proof. pose proof atom_eq_dec. pose proof event_definition_dec. repeat decide equality.  
Qed. 

Record usedVariable: Type :={
  used_var: atom;
  used_eventTagList: list event_definition
}.

Definition usedVariable_dec (n m : usedVariable) : {n = m} + { n <> m}.
Proof. pose proof atom_eq_dec. pose proof event_definition_dec. repeat decide equality.  
Qed. 


(*current state of the monitor*)
Record configuration : Type :={
  datastate : value_env;
  controlstate : scenario_env; 
  raisedevents :  list raisedEvent; (*all raised events, removed after being handled*)
  exportedevents: list raisedEvent; (*only for exported events*)
  finishedscenarios: list scenario;(*no change, using more strict definition*)
  srcstatefinishedscenarios: list (scenario * scenario_state * event_definition);
  updatedvariableList : list updatedVariable;
  usedvariableList : list usedVariable
}.

Definition configuration_dec (n m : configuration) : {n = m} + { n <> m}.
Proof. pose proof expr_eq_dec. repeat decide equality.  
Qed. 

Definition scenarioInclusion (conf: configuration) : Prop:=
incl  (finishedscenarios conf) (dom (controlstate conf)).

(*we assume that state update only updates state variables so that domain of (datastate conf) will never change, meaning 
uniq (datastate conf) always holds
Another assumption is that the update will follow the typechecking rule of normal programming languages*)
Record correct_configuration (conf: configuration) : Prop :={
(*ds_uniq: uniq (datastate conf);*)
(*ds_type_check : forall prod, In prod (datastate conf) -> typeCheck prod;*)
cs_non_empty: dom (controlstate conf)<> nil;
sce_state_no_empty: forall sce, In sce (dom (controlstate conf)) -> getScenarioState sce (controlstate conf) <> None;
finish_uniq: uniqList (finishedscenarios conf);
cs_dom_uniq: uniqList (dom (controlstate conf));
inclusion: scenarioInclusion conf
}.


Definition importEventBool (ev:event_definition) : bool := 
if  (eventKind_dec (eventKind ev) Imported) then true else  false.



Fixpoint getEventInstances' (ev:event_definition) (sce_env: scenario_env): list event_instance :=
match sce_env with
| nil => nil
| (s,state)::env'=> mergeList' (transEvMap (Some state, Some ev)) (getEventInstances' ev env') (event_instance_dec)
end. 


Definition getEventInstances (ev:event_definition) (conf: configuration): list event_instance :=
getEventInstances' ev (controlstate conf).

Fixpoint getEventByName (name: string) (elist: list event_definition):  option event_definition := 
match elist with
| nil => None
| e::lst' => if string_dec (eventId e) name then Some e else getEventByName name lst'
end.

Fixpoint getEventFromActions  (lst: list action) : list event_definition :=
match lst with
| nil => nil
| a::lst' => match a with
               | RaiseStmt s exprs => match getEventByName s eventList with
                                                    | None => getEventFromActions lst'
                                                    | Some ev => mergeList' (ev::nil) (getEventFromActions lst') (event_definition_dec)
                                                    end
               | _ => getEventFromActions lst'
              end
end.


Fixpoint getRaised' (ei:  event_instance) (sce_env:scenario_env) : list event_definition :=
match sce_env with
| nil => nil
| (s,state)::env' => match stpStMap (state,ei) with
                             | None => getRaised' ei env'
                             | Some stp => mergeList' (getEventFromActions (stepActions stp)) (getRaised' ei env') (event_definition_dec)
                             end
end. 
                            

Fixpoint getRaised (lst: list event_instance) (sce_env:scenario_env) : list event_definition :=
match lst with
| nil => nil
| ei::lst' => mergeList' (getRaised' ei sce_env) (getRaised lst' sce_env) event_definition_dec
end. 

(*get all variables from an expression*)
Fixpoint getVariables (e:expr) : list atom :=
match e with
| EOr x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| EAnd x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| EEq x y  => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| ENeq x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| ELt x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| ELe x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| EGt x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| EGe x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| EPlus x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| EMinus x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| EMult x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| EDiv x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| EMod x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| EPos x => getVariables x
| ENeg x => getVariables x
| ENot x => getVariables x
| EAtom x => match x with 
                     | AIdent i => (AIdent i)::nil
                     | _ => nil
                     end 
| EIdx _ _ => nil
| EApp a lst' =>  List.fold_left (fun acc e =>app  (getVariables e) acc) lst' nil
| EDot x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)            
end.

Fixpoint getUpdated (lst: list action) : list atom :=
match lst with
| nil => nil
| act::lst' => match act with
                   | StateUpdate (SUAssign (EAtom (AIdent n)) e) => mergeList' ((AIdent n)::nil) (getUpdated lst') (atom_eq_dec) 
                   | _ => getUpdated lst'
                  end
end.


Fixpoint getUsedFromActions (lst: list action) : list atom :=
match lst with
| nil => nil
| act::lst' => match act with
                   | StateUpdate (SUAssign (EAtom (AIdent n)) e) => mergeList' (getVariables e) (getUpdated lst') (atom_eq_dec)    
                   | _ => getUsedFromActions lst'
                  end
end.

Print event_instance. 
Print step.
 

Definition getUpdatedVariablesFromScenario (conf:configuration) (stp:step)  : list atom
:= filterListReverse (dom (datastate conf)) (getUpdated (stepActions stp)) (atom_eq_dec).

Definition getUsedVariablesFromScenario (conf:configuration) (stp:step)  : list atom
:= 
match (eventWhenExpr (stepEvent stp)) with
| None => filterListReverse (dom (datastate conf)) (getUsedFromActions (stepActions stp)) (atom_eq_dec)
| Some e => filterListReverse (dom (datastate conf)) (mergeList' (getVariables e) (getUsedFromActions (stepActions stp)) (atom_eq_dec)) (atom_eq_dec)
end.

Definition getStep  (conf: configuration) (sce: scenario) (e: event_instance) : option step := 
match getScenarioState sce (controlstate conf) with
| None => None
| Some s =>  stpStMap (s,e)
end.




Local Open Scope Z_scope.
Local Open Scope string_scope.



(*get list of events to raise from list of actions*)
Fixpoint getRaisedEventsFromActions (en: value_env) (re:raisedEvent) (actions :list action) : list raisedEvent := 
match actions with
| nil => nil
| action::actions' => match action with
                               | RaiseStmt e exprs => let vlist := calculateExprList en exprs in
                                                                    match vlist with
                                                                    | (Error s) => nil
                                                                    | Result (vlist') => 
                                                                     let event :=  getEventByName e eventList in 
                                                                     match event with
                                                                    | None => getRaisedEventsFromActions en re actions' 
                                                                    | Some ev =>  {|eventDefinition := ev; eventArguments := vlist'; pathEvents := (eventDefinition re) :: (pathEvents re) |} :: getRaisedEventsFromActions en re actions'
                                                                    end 
                                                                    end
                               | _ => getRaisedEventsFromActions en re actions' 
                              end
end
.


(*test if an event definition is in the list*)
Fixpoint In_event_definition (event: event_definition) (lst: list event_definition) :bool :=
match lst with
| nil => false
| e::lst' => if event_definition_dec (event) (e) then true
                else In_event_definition event lst'
end.

(*test if a scenario is in the list*)
(*change to scenario_dec later*)
Fixpoint In_scenario (sce: scenario) (lst: list scenario) :bool :=
match lst with
| nil => false
| e::lst' => if scenario_dec ( sce) ( e) then true
                else In_scenario sce lst'
end.


(*(a: atom) (t: typ) (v: range_typ) (en:value_env):*)
(*Fixpoint getValue (a: atom) (en:value_env) : option range_typ :=*)
(*semantics function*)
(*assume that n will be in the set of state variables*)
Definition updateValue (ven: value_env)  (act: action) : ErrorOrResult :=
match act with
| StateUpdate (SUAssign (EAtom (AIdent n)) e) =>        
         match (evalMonad ven e) with
        | Error e' => Error e'
        | Result (AFloat q) => Result (updateValueEnv (AIdent n) (Float) (Some (inl (inl (inr q)))) ven)
        | Result (AInt i) => Result (updateValueEnv (AIdent n) (Int) (Some (inl (inl (inl i)))) ven)
        | Result (AString s)=> Result (updateValueEnv (AIdent n) (Int) (Some (inl (inr s))) ven)
        | _ => Result ven
        end
| _ => Result ven
end.


Fixpoint updateDataState  (ven: value_env)  (actionList: list action) : ErrorOrResult := 
match actionList with
| nil =>Result (ven)
| action::alist => match   (updateValue  ven action) with
                          | Error s => Error s
                          | Result d => updateDataState d alist
                          end
end.

Definition updateControlState (cs:scenario_env) (sce: scenario) (stp: step) :scenario_env := 
updateScenarioState' sce (pro_state stp) cs.

(*decision procedure of the tuple (scenario,state,ev)*)
Definition scenarioState_dec (n m : (scenario*scenario_state*event_definition)) : {n = m} + { n <> m}.
Proof. pose scenario_dec. pose string_dec.  pose event_definition_dec.  repeat decide equality. 
Qed. 


Fixpoint eventInPath (ev:event_definition) (lst: list event_definition): bool :=
match lst with
| nil => false
| ev'::lst' => if event_definition_dec ev ev' then true else eventInPath ev lst'
end. 

Fixpoint checkUpdateValue' (a:atom) (lst: list updatedVariable) (re:raisedEvent) : bool :=
match lst with
| nil => true
| v::lst' => if (atom_eq_dec a (up_var v)) then eventInPath (eventTag v) (pathEvents re) else checkUpdateValue' a lst' re
end. 


Fixpoint checkUsedValue'' (evList:list event_definition) (pathList: list event_definition) : bool :=
match evList with
| nil => true
| ev::lst' => if eventInPath ev pathList then checkUsedValue'' lst' pathList else false
end. 


Fixpoint checkUsedValue' (a:atom) (lst: list usedVariable) (re:raisedEvent) : bool :=
match lst with
| nil => true
| v::lst' => if (atom_eq_dec a (used_var v)) then checkUsedValue'' (used_eventTagList v) (pathEvents re) else checkUsedValue' a lst' re
end.

Print configuration. 


Fixpoint checkValue (conf:configuration) (re:raisedEvent) (lst: list atom)   : bool :=
match lst with
| nil => true
| a::lst' => if checkUpdateValue' a (updatedvariableList conf) re then checkValue conf re lst' else  false
end.

Fixpoint checkUpdatedUsedValue (conf:configuration) (re:raisedEvent) (lst: list atom) : bool :=
match lst with
| nil => true
| a::lst' => if checkUsedValue' a (usedvariableList conf) re then checkUpdatedUsedValue conf re lst' else  false
end.


Definition checkValueNonDeterminism (conf:configuration) (re:raisedEvent)  (stp:step) :bool :=
let usedVariables :=  getUsedVariablesFromScenario conf stp in
let updatedVariables := getUpdatedVariablesFromScenario conf stp in
checkValue conf re usedVariables &&  
checkValue conf re updatedVariables &&
checkUpdatedUsedValue conf re updatedVariables
.

Fixpoint updateUsedVariables' (lst: list usedVariable) (a: atom) (re:raisedEvent) : option usedVariable
:=
match lst with
| nil => None
| uv::lst' => if atom_eq_dec a (used_var uv) then 
   Some {|used_var := (used_var uv); used_eventTagList:= ( eventDefinition re) :: (used_eventTagList uv) |}
else updateUsedVariables' lst' a re
end. 


Fixpoint updateUsedVariables (lst: list usedVariable) (lstAtom: list atom) (re:raisedEvent)
:  list usedVariable := 
match lstAtom with
| nil => lst
| a::lstAtom' => match  (updateUsedVariables' lst a re) with
                        | None => (updateUsedVariables lst lstAtom' re)
                        | Some uv => uv :: (updateUsedVariables lst lstAtom' re)
                       end
end.


Fixpoint updatedVariable' (lst: list updatedVariable) (a: atom) (re:raisedEvent) : option updatedVariable
:=
match lst with
| nil => None
| uv::lst' => if atom_eq_dec a (up_var uv) then 
   Some {|up_var := (up_var uv); eventTag:= ( eventDefinition re) |}
else updatedVariable' lst' a re
end. 


Fixpoint updateUpdateVariables (lst: list updatedVariable) (lstAtom: list atom) (re:raisedEvent)
:  list updatedVariable := 
match lstAtom with
| nil => lst
| a::lstAtom' => match  (updatedVariable' lst a re) with
                        | None => (updateUpdateVariables lst lstAtom' re)
                        | Some uv => uv :: (updateUpdateVariables lst lstAtom' re)
                       end
end.

Fixpoint newUpdateVariables (lstAtom : list atom) (re:raisedEvent): list updatedVariable :=
match lstAtom with
| nil => nil
| a::lstAtom' => {|up_var := a; eventTag := eventDefinition re |} :: newUpdateVariables lstAtom' re
end.

Fixpoint newUsedVariables (lstAtom : list atom) (re:raisedEvent): list usedVariable :=
match lstAtom with
| nil => nil
| a::lstAtom' => {|used_var := a; used_eventTagList := (eventDefinition re)::nil |} :: newUsedVariables lstAtom' re
end.

Print configuration. 

Fixpoint getAtomFromUpdateList (lst: list updatedVariable) : list atom :=
match lst with
| nil => nil
| uv::lst' => (up_var uv) :: (getAtomFromUpdateList lst')
end.

Definition getNewUpdateVariables (conf:configuration) (re:raisedEvent) (newList: list atom) : list updatedVariable :=
let updatedList := getAtomFromUpdateList (updatedvariableList conf) in
let atomList := filterList updatedList newList atom_eq_dec in
newUpdateVariables atomList re.


Fixpoint getAtomFromUsedList (lst: list usedVariable) : list atom :=
match lst with
| nil => nil
| uv::lst' => (used_var uv) :: (getAtomFromUsedList lst')
end.

Definition getNewUsedVariables (conf:configuration) (re:raisedEvent) (newList: list atom) : list usedVariable :=
let usedList := getAtomFromUsedList (usedvariableList conf) in
let atomList := filterList usedList newList atom_eq_dec in
newUsedVariables atomList re.


Fixpoint removeEvent' (re : raisedEvent) (lst : list raisedEvent) : list raisedEvent :=
match lst with
| nil => nil
| re' :: lst' => if raisedEvent_dec re re' then lst' else re'::(removeEvent' re lst')
end. 


(*update configuration*)
Definition configTransition (env:value_env) (re:raisedEvent) (e:event_instance) (sce : scenario) (stp: step) (conf: configuration) : ErrorOrResult := 
let extended_env := env in
let ds := updateDataState extended_env (stepActions stp) in
match ds with
| Error s => Error s
| Result ds' => let res:= getRaisedEventsFromActions extended_env re (stepActions stp)
in
let updatedAtom := getUpdatedVariablesFromScenario conf (stp) 
in 
let usedAtom := (getUsedVariablesFromScenario conf stp )
in
Result ({|
datastate := ds';
controlstate := updateControlState (controlstate conf) sce stp;
raisedevents := app res  (removeEvent' re ((raisedevents) conf));
exportedevents := app (filter (fun re => EventKind_beq (eventKind (eventDefinition re)) Exported) res) (exportedevents conf);
finishedscenarios := sce::(finishedscenarios conf);
srcstatefinishedscenarios := (sce,(pre_state stp),(eventDefinition re))::(srcstatefinishedscenarios conf);
updatedvariableList := mergeList' 
         (updateUpdateVariables (updatedvariableList conf) updatedAtom re) 
 (getNewUpdateVariables conf re updatedAtom) updatedVariable_dec;
usedvariableList := mergeList'  (updateUsedVariables (usedvariableList conf) usedAtom re) 
                (getNewUsedVariables conf re usedAtom) usedVariable_dec
|})
end.



Fixpoint checkType' (lst: list (scenario*scenario_state*event_definition)) (re:raisedEvent) : bool := 
match lst with
| nil => true
| (sce,ss,ev)::lst' => if inList (event_definition_dec) (eventDefinition re) (stEvMap (Some ss)) then
                                   if  (eventKind_dec (eventKind ev) Exported) then
                                        false
                                  else  if eventKind_dec (eventKind ev) Internal then
                                        false
                                   else 
                                 checkType'  lst' re
                               else
                                 checkType'  lst' re
end. 


Definition checkType (conf:configuration) (re:raisedEvent) : bool := 
checkType' ((srcstatefinishedscenarios conf)) re.

(*check the guard condition*)
Definition evalCondition (en: value_env) (stp: step) (conf : configuration): bool :=
match eventWhenExpr (stepEvent stp) with
                         | None => true
                         | Some expr => match evalMonad en expr with
                                                   | Result (ABool true) => true
                                                   | _ => false
                                                   end
                         end. 

(*validation check: guard && e in conf.raisedevents sce notin conf.finishedscenarios, *)
Definition valid (en: value_env) (e: event_instance) (sce: scenario) (conf:configuration): bool :=
let stp := (getStep conf sce e) in
match stp with
| None => false
| Some stp' => In_event_definition (event (stepEvent stp' )) (map (fun re => eventDefinition re) (raisedevents conf))
                       && eqb (In_scenario sce (finishedscenarios conf)) false && evalCondition en stp'  conf
end. 

(*here we require existance of eventWhenExpr for the reason that multiple event_instances may correspond to this raised event.
We could add  guard expressions to each event. For one without when, we could add a true
*)
Fixpoint findEventInstance (re:raisedEvent) (en:value_env) (elist: list event_instance): option event_instance :=
match elist with
| nil => None
| e::lst' =>  match  (eventWhenExpr e) with
                | None =>  findEventInstance re en lst'
                | Some expr => 
                 let ex_env := createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re) in
                 match ex_env with
                   | Result (env) => 
                                          let extend_env := (extendEnv (env) (en)) in                                             
                                              match evalMonad extend_env expr with
                                                 | Result (ABool true) =>Some e
                                                  | _ => findEventInstance re en lst' 
                                         end
                  | _ => findEventInstance re en lst' 
                end
               end
end.

(*basic rule*)
Definition constructConfig (sce: scenario) (re: raisedEvent) (conf : configuration): ErrorOrResult:=
let sce_state := (getScenarioState sce (controlstate conf)) in
                     match sce_state with
                    | None =>  (Error error1)
                    | Some state =>  
                            let e' :=  findEventInstance re (datastate conf) (transEvMap (Some state , Some (eventDefinition re))) in
                          match e' with 
                          | None =>  Error error3
                          | Some e => 
                            let ex_env' := createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re) in 
                            match ex_env' with
                            |  (Error s) =>  (Error error12)
                            | Result (ex_env) => 
                            let extend_env := (extendEnv (ex_env) (datastate conf)) in
                               if valid extend_env e sce conf
                               then let stp:= (getStep conf sce e) in match stp with 
                                  | None =>  (Error error4)
                                  | Some stp' => if (checkValueNonDeterminism conf re stp') then 
                                                                 match configTransition extend_env re e sce stp' conf with
                                                                | Error s => Error error11
                                                                | Result s => Result s
                                                                end
                                                          else Error error11
                                  end
                              else  (Error error4)
                             end
                         end
                     end
.

Check getScenarioState. 

(*filter scenarios that cannot be triggered by re*)
Fixpoint transformConfig (scs: list scenario) (re: raisedEvent) (conf : configuration):  list scenario :=
match scs with
| nil => scs
| sce::scenarios' => match constructConfig sce re conf with
                              | Result x => sce::transformConfig scenarios' re conf
                              | Error error => if (string_dec error error3) then transformConfig scenarios' re conf
                                                        else  sce::transformConfig scenarios' re conf
                              end
end.

Print transformConfig.

Fixpoint constructConfigList' (scs: list scenario) (re: raisedEvent) (conf : configuration): ErrorOrResult :=
match scs with
| nil => Result (nil)
| sce::scenarios' => match constructConfig sce re conf with
                                | Result conf' => match constructConfigList' scenarios' re conf with
                                                          | Error s => Error s
                                                          | Result (lst) =>  
                              Result ( conf' :: lst)
                                                          end                           
                                | Error s => Error (s)
                              end

end.

(*core method in synchrony rule, find all state machines that can be triggered by re and execute transitions*)
Definition constructConfigList (scs: list scenario) (re: raisedEvent) (conf : configuration): ErrorOrResult :=
let scs' := (filterList (finishedscenarios conf) scs scenario_dec) in
let scs'' :=  transformConfig scs' re conf in 
constructConfigList' scs'' re conf.


(*definition of an error configuration*)
Definition ErrConfig  (e: raisedEvent) (conf: configuration) :Prop:=
In e (raisedevents conf) -> (exists s, constructConfigList (dom (controlstate conf)) e conf = Error (s)). 

(*no data state conflicts*)
Definition noDataConflict  (dso ds1 ds2:value_env): Prop :=
forall s, 
(exists str, AIdent str = s) /\ 
( (getValue s dso <> getValue s ds1) /\ (getValue s dso <> getValue s ds2) -> getValue s ds1 = getValue s ds2).

(*no control state conflicts*)
Definition noControlConflict (cso cs1 cs2 :scenario_env): Prop :=
forall s, getScenarioState s cso <> getScenarioState s cs1 -> getScenarioState s cso <> getScenarioState s cs2 -> getScenarioState s cs1 = getScenarioState s cs2.

(*no conflicts, used in the definition of synchrony rule*)
Definition noConflict (originConf conf1 conf2: configuration): Prop := noDataConflict (datastate originConf) (datastate conf1) (datastate conf2) 
                /\ noControlConflict (controlstate originConf) (controlstate conf1) (controlstate conf2). 

(*merge datastate*)
Fixpoint mergeDataStateFunc  (dso ds1 ds2:value_env) : ErrorOrResult :=
match dso, ds1, ds2 with
| (n1,(t1,v0))::lst0, (n2,(t2,v1))::lst1, (n3,(t3,v2))::lst2 => if atom_eq_dec n1 n2 then 
                                                                                           if atom_eq_dec n1 n3 then 
                                                                                                   if typ_eq_dec t1 t2 then 
                                                                                                        if typ_eq_dec t1 t3 then
                                              let r :=  mergeDataStateFunc lst0 lst1 lst2 in 
                                                match r with
                                                | Error s => Error s
                                                | Result lst =>  if range_typ_dec v1 v2 then  Result ((n1,(t1,v1))::lst)
                                                                                                                              else if ((range_typ_dec v1 v0)) then 
                                                                                                                              Result ((n1,(t1,v2))::lst)
                                                                                                                              else Result ((n1,(t1,v1))::lst)
                                                                  
                                               end
                                                else Error error5 else Error error5 else Error error5 else Error error5
| _,_,_ => Error error6
end.

(*merge controlstate*)
Fixpoint mergeControlStateFunc  (cso cs1 cs2: scenario_env) : ErrorOrResult :=
match cso, cs1, cs2 with
| (sc0,s0)::lst0, (sc1,s1)::lst1, (sc2,s2)::lst2 => if scenario_dec sc0 sc1 then 
                                                                                           if scenario_dec sc0 sc2 then 
                                              let r :=  mergeControlStateFunc lst0 lst1 lst2 in 
                                                match r with
                                                | Error s => Error s
                                                | Result lst =>  if string_dec s1 s2 then  Result ((sc0,s1)::lst)
                                                                                                                              else if ((string_dec s1 s0)) then 
                                                                                                                              Result ((sc0,s2)::lst)
                                                                                                                              else Result ((sc0,s1)::lst)
          
                                                                  
                                               end
                                                else Error error7 else Error error7
| _,_,_ => Error error6
end.


(*merge configuration*)
Definition mergeConfigFunc (config config1 config2 : configuration):  ErrorOrResult:= 
let ds:= mergeDataStateFunc (datastate config) (datastate config1) (datastate config2) 
in match ds with
   | Error s => Error s
   | Result ds' => 
let cs:= mergeControlStateFunc (controlstate config) (controlstate config1) (controlstate config2) 
in  match cs with
   | Error s => Error s
   | Result cs' => 
let raisedEvents := mergeList' (raisedevents config1) (raisedevents config2) (raisedEvent_dec) in
let exportedEvents := mergeList' (exportedevents config1) (exportedevents config2) (raisedEvent_dec) in
let finishedEvents := mergeList' (finishedscenarios config1) (finishedscenarios config2) (scenario_dec) in
Result ({|
datastate := ds';
controlstate :=cs';
raisedevents := raisedEvents;
exportedevents := exportedEvents;
finishedscenarios := finishedEvents;
srcstatefinishedscenarios := mergeList' (srcstatefinishedscenarios config1) (srcstatefinishedscenarios config2) (scenarioState_dec);
updatedvariableList := mergeList' (updatedvariableList config1) (updatedvariableList config2) (updatedVariable_dec);
usedvariableList := mergeList' (usedvariableList config1) (usedvariableList config2) (usedVariable_dec)
|})
end
end.



Fixpoint innerCombineFunc' (originconf: configuration) (conf: option configuration) (confList: (list configuration)): ErrorOrResult:=

match conf with
| None => match confList with
                 | nil => Error error8
                 | conf'::confList' => innerCombineFunc' originconf (Some conf') (confList')
                end
| Some conf' => match confList with
                 | nil => Result conf'
                 | conf''::confList' =>  let rconf := innerCombineFunc' originconf (Some conf'') ( (confList'))  in
                                                  match rconf with
                                                  | Error s => Error s
                                                  | Result rc => mergeConfigFunc originconf conf' rc 
                                                  end
                end

end.



Definition combineFunc  (e: raisedEvent) (conf: configuration): ErrorOrResult := 
if checkType conf e then
match constructConfigList (dom (controlstate conf)) e conf with
| (Error s) => Error s
| Result (lst) => match lst with
                         | nil => Error error9
                         | lst' =>  innerCombineFunc' conf None lst'
                        end
end
else
   Error error10.

Definition conflict (e: raisedEvent) (conf: configuration) :Prop:=
(exists clist, (constructConfigList (dom (controlstate conf)) e conf = 
Result (clist)) /\ exists conf1 conf2, In conf1 clist /\ In conf2 clist /\ ~(noConflict conf conf1 conf2)). 

(*combine configurations having same source configuration and same triggering event*)
Definition synchrony  (conf conf' :configuration) (event:raisedEvent) : Prop :=
In event (raisedevents conf) /\ ~(ErrConfig event conf ) /\  ~(conflict event conf) /\ combineFunc event conf = Result (conf').

(*chain merge rule*)
Inductive chainMerge: configuration -> configuration-> raisedEvent ->  Prop :=
| basic': forall conf conf' event, (importedEvent (eventDefinition event)) ->  synchrony conf conf' event -> chainMerge conf conf' event
| chain': forall conf conf'' conf' event1 event2, chainMerge conf conf' event1 -> synchrony conf' conf'' event2-> chainMerge conf conf'' event1.

(*initial configuration*)
Definition initialConfig  (conf :configuration) : Prop :=
correct_configuration conf /\ (length (raisedevents conf) = S O) 
/\ (forall e,  In e (raisedevents conf) -> importedEvent (eventDefinition e)
/\ (exists sce, In sce (dom (controlstate conf)) 
/\ In (eventDefinition e) ((alphabet) sce)))
/\ (finishedscenarios conf) = nil.


(* transEvMap ((getScenarioState sce (controlstate conf)), Some (eventDefinition e))  = nil)
means that e is not in the alphabet of sce
SMEDL asks for the complete scenario, so if e is in the alphabet of 
sce, then transEvMap should always return a value
*)
Definition finalConfig (conf:configuration):Prop:=
correct_configuration conf /\ ((length (raisedevents conf) = O)  \/ (forall e  , In e (raisedevents conf) -> (~importedOrInternalEvent (eventDefinition e) 
/\  (forall sce, In sce (dom (controlstate conf)) /\ ~ (In sce (finishedscenarios conf)) -> transEvMap ((getScenarioState sce (controlstate conf)), Some (eventDefinition e))  = nil)))).

(*definition of stuck configuration*)
Definition stuckConfig (conf:configuration):Prop:=
(forall e , In e (raisedevents conf) -> (~(exists conf', synchrony conf conf' e))).