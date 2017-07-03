Require Export EnvLibA.
Require Export RelLibA.
Require Export PRelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Import StaticSemA.
Require Import DynamicSemA.
Require Import TRInductA.
Require Import WeakenA.
Require Import TSoundnessA.
Require Import IdModTypeA.
Require Import IdModPip.
Require Import DetermA.
Require Import AbbrevA.
Require Import HoareA.
Require Import THoareA.
Require Import Lib.
Require Import Pip_state.
Require Import Pip_stateLib.
Require Import Coq.Structures.Equalities.
Require Import Coq.Logic.Eqdep.
Import ListNotations.

Module Hoare_writeVirtualInv <: IdModType.

Module VirtualInv := THoare IdModP.
Export VirtualInv.

Definition Id := VirtualInv.Id.
Definition IdEqDec := VirtualInv.IdEqDec.
Definition IdEq := VirtualInv.IdEq.
Definition W := VirtualInv.W.
Definition Loc_PI := VirtualInv.Loc_PI.
Definition BInit := VirtualInv.BInit.
Definition WP := VirtualInv.WP.

(**************************************************)

(******* Program *)

(** WriteVirtualInv -page -index -vaddress : writes the vaddress at key (page,index) in memory *)

Definition xf_writeVirtual (p: page) (i: index) (v: vaddr) : XFun unit unit := {|
   b_mod := fun s _ => (writeVirtualInternal p i v s,tt)
|}.

Instance VT_unit : ValTyp unit.

Definition WriteVirtual (p: page) (i: index) (v: vaddr) : Exp :=
  Modify unit unit VT_unit VT_unit (xf_writeVirtual p i v) (QV (cst unit tt)).  


(******* State properties *)

(******* Useful Lemmas *)

(** beqPairs **)
Lemma beqPairsTrue : 
forall table1 idx1 table2 idx2 , table1 = table2 /\ idx1 = idx2 ->   
beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex = true.
Proof.
intros.
unfold  beqPairs.
simpl.
intuition.
subst.
unfold beqPage, beqIndex.
specialize beq_nat_refl with table2.
specialize beq_nat_refl with idx2.
intros.
symmetry in H,H0.
rewrite H,H0.
auto.
Qed.

(******* Hoare Triple *)

Lemma writeVirtualInvH (p : page) (i:index) (v:vaddr) (fenv: funEnv) (env: valEnv) :
{{fun _ => True}}
fenv >> env >> WriteVirtual p i v
{{fun _ s => readVirtualInternal p i s.(memory) =  Some v}}.
Proof.
unfold THoareTriple_Eval.
intros.
clear H k3 t k2 k1 tenv ftenv.
inversion X;subst.
inversion X0;subst.
repeat apply inj_pair2 in H5.
apply inj_pair2 in H7.
subst.
unfold b_eval, b_exec, xf_writeVirtual, b_mod in *.
simpl in *.
inversion X1;subst.
unfold writeVirtualInternal.
simpl.
unfold add.
unfold readVirtualInternal.
simpl.
specialize beqPairsTrue with p i p i.
intros.
intuition.
rewrite H0.
reflexivity.
inversion X2.
inversion X2.
Qed.







End Hoare_writeVirtualInv.
