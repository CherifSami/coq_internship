Require Export Basics.

Require Export EnvListAux7.
Require Export EnvListAuxT1.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Import TPipStaticM2.
Require Import TPipDynamicM2.


Module Weakening (IdT: IdModType) <: IdModType.
(* Export IdT. *)

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module DynamicC := Dynamic IdT.
Export DynamicC.



Lemma QValWeakening (env env': valEnv)
      (n1 n2: W)
      (q1 q2: QValue):
  QVStep env (Conf QValue n1 q1) (Conf QValue n2 q2) ->
  QVStep (overrideE env env') (Conf QValue n1 q1) (Conf QValue n2 q2).
Proof.
  intros. 
  inversion X; subst.
  constructor.
  inversion X0; subst.
  eapply overrideRedux1 with (env2:=env') in H.
  constructor.
  rewrite H.
  inversion X0; subst.
  assumption.
Defined.


Lemma QFunWeakening (env env': funEnv)
      (n1 n2: W)
      (q1 q2: QFun):
  QFStep env (Conf QFun n1 q1) (Conf QFun n2 q2) ->
  QFStep (overrideE env env') (Conf QFun n1 q1) (Conf QFun n2 q2).
Proof.
  intros. 
  inversion X; subst.
  constructor.
  inversion X0; subst.
  eapply overrideRedux1 with (env2:=env') in H.
  constructor.
  rewrite H.
  inversion X0; subst.
  assumption.
Defined.
  

Lemma weak 
           (fenv fenv': funEnv) (env env': valEnv)
           (n1 n2: W) (e1 e2: Exp):
      EClosure fenv env (Conf Exp n1 e1) (Conf Exp n2 e2) ->
      EClosure (overrideE fenv fenv') (overrideE env env')
               (Conf Exp n1 e1) (Conf Exp n2 e2).
Proof.
  intros.  
  dependent induction X.
  constructor.
  destruct p2 as [n0 e0].
  specialize (IHX n0 n2 e0 e2 eq_refl eq_refl).
  econstructor.
  Focus 2.
  eassumption.

  (***)

  clear IHX.
  clear X.
  rename e into H.
  clear n2 e2.
  revert fenv' env'.
  
  (***)

    eapply (EStep_mut (fun fenv env c1 c2
 (ExIH: EStep fenv env c1 c2) => forall fenv' env',    
  EStep (overrideE fenv fenv') (overrideE env env') 
        c1 c2)
  (fun fenv env c1 c2
  (PsIH: PrmsStep fenv env c1 c2) => forall fenv' env', 
  PrmsStep (overrideE fenv fenv') (overrideE env env') 
           c1 c2)).

  - intros.
    constructor.
  - intros.                     
    constructor.
    eapply QValWeakening.
    assumption.
  - intros.
    constructor.
  - intros.
    constructor.
    eapply QValWeakening.
    assumption.
  - intros.
    constructor.
  - intros.
    constructor.
    eapply X.
  - intros.    
    constructor.    
  - intros.  
    constructor.    
    eapply X.
  - intros.        
    constructor. 
  - intros. 
    econstructor.
    + reflexivity.
    + reflexivity.
    + rewrite overrideAssoc.
      rewrite overrideAssoc.
      specialize (X fenv'0 env'0).
      rewrite e2 in X.
      rewrite e3 in X.
      eapply X. 
  - intros.
    econstructor.
    auto.
    eassumption.
    assumption.
    assumption.
  - intros.
    econstructor.
    eassumption.
    assumption.
    assumption.
  - intros.  
    econstructor.
    eapply X.    
  - intros.
    econstructor.
    eapply QFunWeakening.       
    assumption.    
  - intros.
    constructor.
  - intros.
    constructor.
  - intros.
    constructor.
    eapply X.
  - intros.
    constructor.
    eapply X.                 
  - intros.
    constructor.      
    eapply X.     
  - assumption.
Defined.    

End Weakening.

