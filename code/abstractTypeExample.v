Require Import  Coq.Lists.List. 


Definition insert (n:nat) (lst: list nat) :list nat := n::lst. 

Definition remove (lst: list nat) : ((option nat) * list nat) :=
match rev(lst) with
| nil => (None, nil)
| l::lst' => (Some l,lst')
end. 




Definition listProd: Set := (list nat * list nat) %type. 

Definition insert' (n:nat) (lst: listProd) :listProd := 
match lst with
| (bs,fs) => (n::bs,fs)
end. 

Definition remove' (lst:listProd): ((option nat) * listProd) :=
match lst with
| (bs , nil) => match rev(bs) with 
                    | nil => (None,lst)
                    | i::bs' => (Some i, (nil,bs'))
                    end
| (bs, f::fs') => (Some f, (bs,fs'))
end.

Definition R (lst: list nat) (lstProd:listProd) : Prop :=
let (bs,fs):=lstProd in
lst = app (bs) (rev(fs)).

Lemma emptyR: 
R nil (nil,nil).
Proof.  simpl. auto. Qed.



Lemma insertR:
forall lst lstProd d, R lst lstProd -> R (insert d lst) (insert' d lstProd).
Proof.
intros.  unfold R. 
unfold insert. destruct lstProd. 
simpl. inversion H. auto.  
Qed. 

Lemma removeR:
forall lst lstProd, 
R lst lstProd -> 
(lst = nil /\ lstProd = (nil,nil) 
\/ (exists d d' lst' lstProd',  remove lst = (Some d,lst') -> remove' lstProd =(Some d', lstProd') -> R lst' lstProd')).
Proof.
intros. destruct lstProd.
destruct l0. destruct l. inversion H. left. split; simpl; auto.
inversion H. simpl in H0. right.
exists n. exists n. exists l.   exists ((nil,rev l)).
intros. unfold R. simpl. rewrite rev_involutive.   auto.
inversion H. right.
exists n.  exists n. exists (l++ rev l0). 
exists ((l,l0)).
intros. unfold R. auto.
Qed.       






