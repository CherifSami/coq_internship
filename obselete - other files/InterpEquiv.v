
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
Require Import TRInductM2.
Require Import WeakM2.

Require Import TSoundnessRM2.
Require Import ReflectInterpM2. 
Require Import SOS2Gallina.
Require Import IdModType.


Module IEquiv (IdT: IdModType) <: IdModType.
Export IdT.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module SOS2GallC := SOS2Gall IdT.
Export SOS2GallC.


(*
Program Definition SOS_Exp (Z: Type) (PZ: PState Z)
                   (fenv: funEnv) (env: valEnv)
                   (e: Exp) (t: VTyp) (n: Z) 
                   (k: SoundExp Z PZ fenv env e t n) (n: Z) :
                              prod (vtypExt t) Z := _.
*)

Definition InterEquivExp 
         (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (e: Exp) (t: VTyp) (k0: ExpTyping ftenv tenv fenv e t) 
         (k1: FEnvTyping fenv ftenv)   
         (env: valEnv)
         (k2: EnvTyping env tenv) (n: W) :=  
         Exp_Trans ftenv tenv fenv e t k0 k1 env k2 n = 
         SOS_Exp fenv env e t n 
                 (ExpEval ftenv tenv fenv e t k0 k1 env k2 n).


Definition InterEquivPrms  
         (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (ps: Prms) (pt: PTyp) (k0: PrmsTyping ftenv tenv fenv ps pt) 
         (k1: FEnvTyping fenv ftenv)   
         (env: valEnv)
         (k2: EnvTyping env tenv) (n: W) :=  
         Prms_Trans ftenv tenv fenv ps pt k0 k1 env k2 n = 
         SOS_Prms fenv env ps pt n 
                 (PrmsEval ftenv tenv fenv ps pt k0 k1 env k2 n).


Definition InterEquivFun 
         (f: Fun) (ft: FTyp) (k0: FunTyping f ft) 
         (env: valEnv) 
         (k1: EnvTyping env (extParType ft)) (n: W) :=
         Fun_Trans f ft k0 (WT_valEnv_Trans (extParType ft) env k1) n = 
         SOS_Fun f ft n k0 env (FunEval f ft k0 env k1 n).


Definition InterEquivQFun
         (ftenv: funTC) (fenv: funEnv)
         (q: QFun) (ft: FTyp) 
         (k0: QFunTyping ftenv fenv q ft)
         (k1: FEnvTyping fenv ftenv)   
         (env: valEnv) 
         (k2: EnvTyping env (extParType ft)) (n: W) :=  
  QFun_Trans ftenv fenv q ft k0 k1 
             (WT_valEnv_Trans (extParType ft) env k2) n = 
         SOS_QFun ftenv fenv q ft n k0 env   
                          (QFunEval ftenv fenv q ft k0 k1 env k2 n).


(*****************************)


Definition InterEquivExpP  
         (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (e: Exp) (t: VTyp) (k0: ExpTyping ftenv tenv fenv e t) :=
 forall (k1: FEnvTyping fenv ftenv)   
        (env: valEnv)
        (k2: EnvTyping env tenv) (n: W),
   InterEquivExp ftenv tenv fenv e t k0 k1 env k2 n.


Definition InterEquivPrmsP  
         (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (ps: Prms) (pt: PTyp) (k0: PrmsTyping ftenv tenv fenv ps pt) := 
  forall (k1: FEnvTyping fenv ftenv)   
         (env: valEnv)
         (k2: EnvTyping env tenv) (n: W),
   InterEquivPrms ftenv tenv fenv ps pt k0 k1 env k2 n.  


Definition InterEquivFunP 
           (f: Fun) (ft: FTyp) (k0: FunTyping f ft) :=
   forall (env: valEnv) 
          (k1: EnvTyping env (extParType ft)) (n: W),
     InterEquivFun f ft k0 env k1 n.


Definition InterEquivQFunP
         (ftenv: funTC) (fenv: funEnv)
         (q: QFun) (ft: FTyp) 
         (k0: QFunTyping ftenv fenv q ft) :=
  forall (k1: FEnvTyping fenv ftenv)   
         (env: valEnv) 
         (k2: EnvTyping env (extParType ft)) (n: W),
     InterEquivQFun ftenv fenv q ft k0 k1 env k2 n.

Definition ExpTypingIEq_rect :=
  ExpTyping_str_rect 
                     InterEquivFunP InterEquivQFunP 
                     InterEquivExpP InterEquivPrmsP. 

(****************************************)

Lemma InterpreterExpEquivalence (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
      (e: Exp) (t: VTyp) (k0: ExpTyping ftenv tenv fenv e t) :
  InterEquivExpP ftenv tenv fenv e t k0.
  eapply ExpTypingIEq_rect.
  intros.
  unfold Par_SSL.
  unfold InterEquivExpP.
  constructor.
  (**)
  intros.
  unfold Par_SSL.
  unfold InterEquivExpP.
  unfold InterEquivExp.
  unfold InterEquivExpP in H.
  unfold InterEquivExp in H.
  econstructor.
  exact H.
  auto.
  (**)
    unfold Par_SSA.
    constructor.
    unfold Par_SSA.
    unfold InterEquivFunP.
    unfold InterEquivFun.
    intros.
    econstructor.
    exact H.
    exact X.
  (**)  
    unfold Par_SSA.
    unfold InterEquivFunP.
    unfold InterEquivFun.
    intros.
    unfold Par_SSB.
    econstructor.
    exact h2.
    exact h3.
    unfold Par_SSA.
    exact X.
    unfold Par_SSA.
    exact X0.
    exact H.
    Unshelve.
    Focus 14.
    exact m0.
    Focus 14.
    exact m1.
  (**) 
    unfold InterEquivExpP.
    unfold InterEquivExp.
    unfold InterEquivFunP.
    unfold InterEquivFun.
    intros.
    specialize (H m env k1 n).
  (**)
    Focus 3.  
    intros.
    unfold InterEquivQFunP.
    unfold InterEquivQFun.
    intros.
    destruct ft.
    destruct f.    
    inversion k; subst.
    Unfocus.
   (**)
    Focus 7.
    intros.
    unfold InterEquivExpP.
    unfold InterEquivExp.
    intros.

Admitted.
    
    
(*    
    destruct (SOS_Fun (FC fenv0 tenv0 e0 e1 x 0) (FT tenv0 t0) n
    (FunZ_Typing ftenv0 tenv0 fenv0 e0 e1 x t0 m k) env
    (FunEval (FC fenv0 tenv0 e0 e1 x 0) (FT tenv0 t0)
       (FunZ_Typing ftenv0 tenv0 fenv0 e0 e1 x t0 m k) env k1 n)).
    Focus 2.
*)    

(*
Lemma InterpreterExpEquivalence (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
      (e: Exp) (t: VTyp) (k0: ExpTyping ftenv tenv fenv e t) :
  InterEquivExpP ftenv tenv fenv e t k0.
  eapply ExpTypingIEq_rect.
  - intros.
    unfold Par_SSL.
    unfold InterEquivExpP.
    constructor.
  - intros.
    unfold Par_SSL.
    unfold InterEquivExpP.
    unfold InterEquivExp.
    unfold InterEquivExpP in H.
    unfold InterEquivExp in H.
    econstructor.
    exact H.
    auto.
  - unfold Par_SSA.
    constructor.
  - unfold Par_SSA.
    unfold InterEquivFunP.
    unfold InterEquivFun.
    intros.
    econstructor.
    exact H.
    exact X.
  - unfold Par_SSA.
    unfold InterEquivFunP.
    unfold InterEquivFun.
    intros.
    econstructor.
    exact h2.
    exact h3.
    unfold Par_SSA.
    exact X.
    unfold Par_SSA.
    exact X0.
    exact H.
  - unfold InterEquivExpP.
    unfold InterEquivExp.
    unfold InterEquivFunP.
    unfold InterEquivFun.
    intros.
    specialize (H m env k1 n).
    destruct ((FunEval (FC fenv0 tenv0 e0 e1 x 0) (FT tenv0 t0)
       (FunZ_Typing ftenv0 tenv0 fenv0 e0 e1 x t0 m k) env k1 n)).

    
    unfold SOS_Exp in H.

    simpl.
    
    compute.
    
    cut ( Exp_Trans ftenv0 tenv0 fenv0 e0 t0 k m env k1 n =
          Fun_Trans (FC fenv0 tenv0 e0 e1 x 0) (FT tenv0 t0)
                (FunZ_Typing ftenv0 tenv0 fenv0 e0 e1 x t0 m k)
                (WT_valEnv_Trans (extParType (FT tenv0 t0)) env k1) n ).
    intro.
    rewrite <- H0.
    rewrite H.
    compute.
    auto.
    

    
    unfold SOS_Fun. 
    
    simpl.
    
    unfold WT_valEnv_Trans.
    unfold Fun_Trans.
    unfold SOS_Fun.
    destruct (FunZ_Typing ftenv0 tenv0 fenv0 e0 e1 x t0 m k).
*)    
 
End IEquiv.