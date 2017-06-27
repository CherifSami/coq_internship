Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Eqdep FunctionalExtensionality Coq.Program.Tactics.
Require Import TPipStaticM2. 
Require Import IdModType.
Require Import IdMod2.
Import ListNotations.

Open Scope string_scope.

(* Essayons de convertir la fonction suivante, de type : page -> LLI page *)
(* Definition getPd partition := *)
(*   perform idxPD := getPDidx in *)
(*   perform idx := MALInternal.Index.succ idxPD in *)
(*   readPhysical partition idx. *)

(*
Definition TPipStatic20.Id := string.
 *)

Module Convert2.

Module Static2 := Static IdModM2.
Export Static2.

(* Definition L: string -> Id := id. *)
  

Definition PartitionType := vtyp nat. 

Definition IdxType := vtyp nat. 

Definition VLift := Return LL.

(*** to be implemented using Modify *)
Variable IndexSuccImpl : QValue -> Exp.

Variable ReadPhysicalImpl : QValue -> QValue -> Exp.
(***)


Definition IndexSucc : Fun := FC
                             nil 
                             [("i_arg", IdxType)]
                             (ReadPhysicalImpl (Var "p_arg")
                                               (Var "i_arg"))
                             (Val (cst nat 0))
                             ("ReadPhysical")
                             0.

Definition ReadPhysical : Fun := FC
                             nil
                             [("p_arg", PartitionType);("i_arg", IdxType)]
                             (ReadPhysicalImpl (Var "p_arg")
                                               (Var "i_arg"))
                             (Val (cst nat 0))
                             "ReadPhysical"
                             0.

Definition PerformIdxInReadPhysical : Exp :=
  BindS "idxPD"
        (VLift (Var "getPDix"))
        (BindS "idx"
               (Apply (FVar "IndexSucc")
                      (PS [(VLift (Var "idxPD"))]))
               (Apply (QF ReadPhysical)
                      (PS [(VLift (Var "partition"));
                           (VLift (Var "idx"))]))).

Definition getPd : Fun := FC
       [("ReadPhysical", ReadPhysical); ("IndexSucc", IndexSucc)]         
       [("partition", PartitionType)] 
       PerformIdxInReadPhysical
       (Val (cst nat 0))
       "getPd"
       0.


(*****************************************************************)


Definition state : Type := nat.

Definition M (A : Type) : Type := state -> A * state.

Definition ret {A : Type} (a : A) : M A :=
  fun s => (a , s).

Definition bind {A B : Type} (m : M A)(f : A -> M B) : M B :=  
fun s => match m s with
    | (a, s') => f a s'
    end.


Fixpoint iterate {A B : Type} (f0 : A -> M B)
                                (f1: (A -> M B) -> (A -> M B))
                                (n: nat) (a: A) : M B :=
  match n with
    | 0 => f0 a
    | S n' => f1 (iterate f0 f1 n') a 
  end.                    


(* exmaple 1 *)

Fixpoint fact (n: nat) : nat :=
  match n with 0 => 1 | (S m) => (S m) * fact m end.

Definition fact0 := fun n:nat => 1. 

Definition fact1 := fun (f: nat -> nat) (n: nat) =>
                      match n with 0 => 1 | (S m) => (S m) * f m end.

Definition factM0 := fun n:nat => ret 1. 

Definition factM1 := fun (f: nat -> M nat) (n: nat) =>
                       match n with 0 => ret 1 | (S m) =>
                              bind (f m) (fun x => ret (x * (S m))) end.

Definition factM (n: nat) := iterate factM0 factM1 n n.   

(* exmaple 2 *)

Fixpoint lengthN (ls: list nat) : nat :=
  match ls with [] => 0 | h::tl => 1 + lengthN tl end.   

Definition lengthN0 := fun ls: list nat => 0.

Definition lengthN1 := fun (f: list nat -> nat) (ls: list nat) =>  
           match ls with [] => 0 | h::tl => 1 + f tl end. 

Definition lengthNM0 := fun ls: list nat => ret 0.

Definition lengthNM1 := fun (f: list nat -> M nat) (ls: list nat) =>  
                          match ls with [] => ret 0 | h::tl =>
                              bind (f tl) (fun x => ret (x + 1)) end. 

Definition lengthNM (n: nat) (ls: list nat) :=
                          iterate lengthNM0 lengthNM1 n ls.   

(* example 3 *)

Fixpoint dummyRec timeout (arg : nat) : M nat :=
  match timeout with
  | 0 => ret arg
  | S timeout1 =>
    bind (ret (S arg)) (dummyRec timeout1)
  end.       


Definition dummyRecI0 := fun n:nat => ret n. 

Definition dummyRecI1 := fun (f: nat -> M nat) (n: nat) =>
                                        bind (ret (S n)) f.

Definition dummyRecI timeout (arg : nat) : M nat :=
  iterate dummyRecI0 dummyRecI1 timeout arg.

Lemma dummyEq (timeout arg : nat) :
  dummyRec timeout arg = dummyRecI timeout arg. 
  revert arg.
  induction timeout.
  auto.
  intros.
  simpl.
  simpl.
  unfold bind.
  simpl.
  eapply functional_extensionality_dep.
  rewrite IHtimeout.
  intros.
  reflexivity.
Qed.  


Definition dummyRecD0 (n: nat) : Exp := Val (cst nat n).

Definition dummyRecD1 (x: Id) (y: Id) (n: nat) : Exp :=
      BindS x (Val (cst nat (S n))) (Apply (FVar y) (PS [VLift (Var x)])). 


Definition dummyRecD (arg timeout: nat) : Fun := FC
                                nil
                                [("arg", Nat)]
                                (dummyRecD0 arg)
                                (dummyRecD1 "arg" "dummyRec" arg)
                                "dummyRec"
                                timeout.

End Convert2.

(*

(* il faudrait bien commencer par définir l’ensemble des identifiants possibles ?
   est-ce que tricher avec un type comme string serait faisable ? *)
Inductive Id : Type := partition | idxPD | idx.
(* Mais je n’arrive pas à créer de valeur de type TPipStatic20.Id, qui
   est le type attendu, est-ce normal ? *)

(* comment se fait qu’About Fun n’indique pas de dépendance à un type Id ? *)
Definition corps : Exp.
Admitted.

Definition getPdFun : Fun := FC nil nil corps corps partition 0.
  (* FC : pas d’autre choix de toute façon *)
  (* [] : pas d’environnements, si ? que pourraient-ils contenir ? *)
  (* [] : des constantes, comme par exemple la valeur de N ? *)
  (* corps *)
  (* corps : ici, il n’est pas nécessaire de faire une différence entre les cas 0 et 1, si ? *)
  (* partition : c’est bien l’argument ? *)
  (* 0. *)

*)