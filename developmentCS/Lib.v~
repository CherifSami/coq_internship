Require Import List NPeano Omega Coq.Logic.Classical_Prop Bool.
Import List.ListNotations.

(** * Summary 
    This file contains required functions to manipulate an association list *) 

Fixpoint eqList {A : Type} (l1 l2 : list A) (eq : A -> A -> bool) : bool := 
 match l1, l2 with 
 |nil,nil => true
 |a::l1' , b::l2' => if  eq a b then eqList l1' l2' eq else false
 |_ , _ => false
end.

Definition beqPairs {A B: Type} (a : (A*B)) (b : (A*B)) (eqA : A -> A -> bool) (eqB : B -> B -> bool) :=
if (eqA (fst a) (fst b)) && (eqB (snd a) (snd b))  then true else false.

Fixpoint lookup {A B C: Type} (k : A) (i : B)  (assoc : list ((A * B)*C))  (eqA : A -> A -> bool) (eqB : B -> B -> bool) :=
  match assoc with
    | nil => None  
    | (a, b) :: assoc' => if beqPairs a (k,i) eqA eqB then Some b else lookup k i assoc' eqA eqB
  end. 
 
Fixpoint removeDup {A B C: Type} (k : A) (i : B) (assoc : list ((A * B)*C) )(eqA : A -> A -> bool) (eqB : B -> B -> bool)   :=
  match assoc with
    | nil => nil
    | (a, b) :: assoc' => if beqPairs a (k,i) eqA eqB then removeDup k i assoc' eqA eqB else (a, b) :: (removeDup k i assoc' eqA eqB)
  end.

Definition add {A B C: Type} (k : A) (i : B) (v : C) (assoc : list ((A * B)*C) ) (eqA : A -> A -> bool) (eqB : B -> B -> bool)  :=
  (k,i,v) :: removeDup k i assoc eqA eqB.
