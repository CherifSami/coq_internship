Require Export Basics.

Require Export EnvListAux7.
Require Export EnvListAuxT1.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Import Coq.Logic.ProofIrrelevance.

Require Import TPipStaticM2.
Require Import TPipDynamicM2.
Require Import TRInductM2.
Require Import WeakM2.
Require Import TSoundnessM2.
Require Import IdModType.
Require Import IdMod2.

Module Test2 (*IdT: IdModType*) <: IdModType.

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

Definition xf_read : XFun unit W := {|
   b_mod := fun x _ => (x, x)     
|}.                                                     

Definition xf_write : XFun W unit := {|
   b_mod := fun _ x => (x, tt)     
|}.                                                     

Definition xf_reset : XFun (PState W) unit := {|
   b_mod := fun x _ => (b_init, tt)     
|}.                                                     


(*Definition xf_nat_read : XFun unit W := xf_read.          

Definition xf_nat_write : XFun W unit := xf_write.        

Definition xf_nat_reset : XFun (PState W) unit := xf_reset.                                                     
Definition xf_nat_resetE : XFun (PState W) unit := {|
   b_mod := fun (x:W) (psn: PState W) => (@b_init W psn, tt)     
|}.                                                     

 Definition C: W -> nat := id. *)
  
Definition xf_nat_incr : XFun W unit := {|
   b_mod := fun x y => (x+y, tt)     
|}.                                                     

(*
Variable StTy: Type.
Variable StTy_inst : PState StTy.
Variable InTy OutTy: Type.
Variable StTy_Exec : StTy -> (prod InTy (PState StTy)) -> StTy.
Variable StTy_Eval : StTy -> (prod InTy (PState StTy)) -> OutTy.

Definition xf_StTy_mod : XFun (prod InTy (PState W)) OutTy := {|
   b_mod := fun s i => (StTy_Exec s i, StTy_Eval s i)     
|}.                                                     
*)

Instance PSNatV : ValTyp (PState nat).

Definition Read (VW: ValTyp W) : Exp :=
  Modify unit W UnitV VW xf_read (QV (cst unit tt)).

Definition Write (VW: ValTyp W) (x: nat) : Exp :=
  Modify W unit VW UnitV xf_write (QV (cst nat x)).

Definition Reset (VW: ValTyp (PState W)) : Exp :=
  Modify (PState W) unit VW UnitV xf_reset
         (QV (cst (PState nat) pstate_nat)).


Definition ReadN : Exp := Read NatV.

Definition WriteN (x: nat) : Exp := Write NatV x.

Definition ResetN : Exp := Reset PSNatV.

Definition Incr (x: nat) : Exp :=
  Modify nat unit NatV UnitV xf_nat_incr (QV (cst nat x)).




Lemma expTypingTest1 : ExpTyping emptyE emptyE emptyE
                                 (BindN ResetN ReadN) Nat.
  econstructor.
  econstructor.
  econstructor.
  constructor.
  simpl.
  auto.
  simpl.
  apply PSNatV.
  constructor.
  constructor.
  constructor.
  simpl.
  auto.
  simpl.
  apply UnitV.
Defined.


Lemma fenvTypingTest1 : FEnvTyping emptyE emptyE.
  constructor.
Defined.

Lemma envTypingTest1 : EnvTyping emptyE emptyE.
  constructor.
Defined.

Definition Test1 (n: nat) :=  projT1 (sigT_of_sigT2 
 (WellTypedEvalM emptyE emptyE emptyE (BindN ResetN ReadN) Nat
  expTypingTest1 fenvTypingTest1 emptyE envTypingTest1 n)). 


Lemma Test1L (n: nat) : Test1 n = cst nat 0.
  auto.
Qed.



Definition FunTypingI f t := FunTyping t f.

Definition QFunTypingI ftenv fenv q t :=
           QFunTyping ftenv fenv t q.

Definition ExpTypingI ftenv tenv fenv e t :=
           ExpTyping ftenv tenv fenv t e.

Definition PrmsTypingI ftenv tenv fenv ps ts :=
           PrmsTyping ftenv tenv fenv ts ps.

Definition FEnvTypingI fenv ftenv :=
           FEnvTyping ftenv fenv.

Definition ProgTypingI ftenv fenv p t :=
           ProgTyping ftenv fenv t p.


Definition FunTypingNN := FunTypingI.

Definition QFunTypingNN := QFunTypingI.

Definition ExpTypingNN := ExpTypingI.

Definition PrmsTypingNN := PrmsTypingI.

Definition FEnvTypingNN := FEnvTypingI.

Definition ProgTypingNN := ProgTypingI.


Definition FunTypingN := FunTyping.

Definition QFunTypingN := QFunTyping.

Definition ExpTypingN := ExpTyping.

Definition PrmsTypingN := PrmsTyping.

Definition FEnvTypingN := FEnvTyping.

Definition ProgTypingN := ProgTyping.

End Test2.