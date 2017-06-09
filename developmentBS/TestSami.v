Require Export Basics.

Require Export EnvListAux7.
Require Export EnvListAuxT1.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Logic.ProofIrrelevance.

Require Import TPipStaticM2.
Require Import TPipDynamicM2.
Require Import TRInductM2.
Require Import WeakM2.
Require Import TSoundnessM2.
Require Import IdModType.
Require Import IdMod2.


Module TSoundness2 := TSoundness IdModM2.
Export TSoundness2.

Definition Id := TSoundness2.Id.
Definition IdEqDec := TSoundness2.IdEqDec.
Definition IdEq := TSoundness2.IdEq.
Definition W := TSoundness2.W.
Definition Loc_PI := TSoundness2.Loc_PI.
Definition BInit := TSoundness2.BInit.
Definition WP := TSoundness2.WP.

(**************************************************)

Lemma fenvTyping : FEnvTyping emptyE emptyE.
  constructor.
Defined.

Lemma envTyping : EnvTyping  emptyE emptyE.
  constructor.
Defined.


(**************************************************)

(* line 1 : if true then 3 else 3) *)

Definition three:Exp := Val(cst nat 3).
Definition truth:Exp := Val (cst bool true).
Definition line1:Exp := IfThenElse truth three three.
Lemma expTypingline1 : ExpTyping emptyE emptyE emptyE line1 Nat.
Proof.
repeat try (econstructor;auto).
Defined.

Definition line1Test (n: nat) :=  projT1 (sigT_of_sigT2 
 (WellTypedEvalM emptyE emptyE emptyE line1 Nat
  expTypingline1 fenvTyping emptyE envTyping n)).

Lemma Test1 (n: nat) : line1Test n = cst nat 3.
auto.
Qed.


(**************************************************)

(* line 2 : apply add3 to 0*)

Open Scope string_scope.

Definition zero:Exp := Val(cst nat 0).

Definition xf_add3 : XFun nat nat := {|
   b_mod := fun st x => (2,2)
|}.
Definition add3':Exp := Modify nat nat NatV NatV xf_add3 (Var "x").
Definition add3:QFun := QF(FC emptyE [("x",Nat)] add3' zero "add3" 0).
Definition line2:Exp := Apply add3 (PS [zero]). 
  
Lemma expTypingline2 : ExpTyping emptyE emptyE emptyE line2 Nat.
Proof.
repeat econstructor.
Defined.


Definition line2Test (n: nat) :=  projT1 (sigT_of_sigT2 
 (WellTypedEvalM emptyE emptyE emptyE line2 Nat
  expTypingline2 fenvTyping emptyE envTyping n)).

Lemma Test2 (n: nat) : line2Test n = cst nat 3.
Admitted.


(**************************************************)

(* line 3 : BindN line1 line2*)

Definition line3:Exp := BindN line1 line2.
Lemma expTypingline3 : ExpTyping emptyE emptyE emptyE line3 Nat.
Proof.
econstructor.
eapply expTypingline1.
apply expTypingline2.
Defined.


Definition line3Test (n: nat) :=  projT1 (sigT_of_sigT2 
 (WellTypedEvalM emptyE emptyE emptyE line3 Nat
  expTypingline3 fenvTyping emptyE envTyping n)).

Lemma Test3 (n: nat) : line3Test n = cst nat 3.
Admitted.


(**************************************************)

(* line 4 : BindN zero line1*)

Lemma expTypingzero : ExpTyping emptyE emptyE emptyE zero Nat.
Proof.
constructor.
constructor.
auto.
constructor.
Defined.

Definition line4:Exp := BindN zero line1.
Lemma expTypingline4 : ExpTyping emptyE emptyE emptyE line4 Nat.
Proof.
econstructor.
eapply expTypingzero.
apply expTypingline1.
Defined.


Definition line4Test (n: nat) :=  projT1 (sigT_of_sigT2 
 (WellTypedEvalM emptyE emptyE emptyE line4 Nat
  expTypingline4 fenvTyping emptyE envTyping n)).

Lemma Test4 (n: nat) : line4Test n = cst nat 3.
auto.
Qed.


(**************************************************)

(*line 6 : if (Apply est_0 0) then zero else three*)

Definition xf_est_0 : XFun nat bool := {|
   b_mod := fun st x => (st,if beq_nat x 0 then true else false)
|}.
Definition est_0':Exp := Modify nat bool NatV BoolV xf_est_0 (Var "x").
Definition est_0:QFun := QF(FC emptyE [("x",Nat)] est_0' zero "est_0" 0).
Definition line6:Exp := IfThenElse (Apply est_0 (PS [zero])) zero three.
  
Lemma expTypingline6 : ExpTyping emptyE emptyE emptyE line6 Nat.
Proof.
repeat econstructor.
Defined.

Definition line6Test (n: nat) :=  projT1 (sigT_of_sigT2 
 (WellTypedEvalM emptyE emptyE emptyE line6 Nat
  expTypingline6 fenvTyping emptyE envTyping n)).

Lemma Test6 (n: nat) : line6Test n = cst nat 0.
Admitted.

(**************************************************)

Definition ret_x : Exp := Return RR (Var "x").
Definition line7 : Exp := BindS "x" zero ret_x.
Lemma expTypingline7 : ExpTyping emptyE emptyE emptyE line7 Nat.
Proof.
econstructor.
constructor.
eapply expTypingzero.
repeat constructor.
Defined.

Definition line7Test (n: nat) :=  projT1 (sigT_of_sigT2 
 (WellTypedEvalM emptyE emptyE emptyE line7 Nat
  expTypingline7 fenvTyping emptyE envTyping n)).

Lemma Test7 (n: nat) : line7Test n = cst nat 0.
auto.
Qed.


