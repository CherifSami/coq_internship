
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
Require Import IdModType.

Module SOS2Gall (IdT: IdModType) <: IdModType.
Export IdT.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module ReflectC := Reflect IdT.
Export ReflectC.


Program Definition SOS_Exp 
                   (fenv: funEnv) (env: valEnv)
                   (e: Exp) (t: VTyp) (n: W) 
                   (k: SoundExp fenv env e t n) :
                              prod (vtypExt t) W := _.

Next Obligation.
  unfold SoundExp in k.
  destruct k.
  split.
  - inversion v; subst.
    subst T.
    rewrite H in H0.
    assert (projT1 x).
    exact (cstExt x).
    unfold vtypExt.
    rewrite <- H.
    exact X.
  - destruct s.
    exact x0.
Defined.    



Program Definition SOS_Fun
        (f: Fun) (ft: FTyp) (n: W)
        (k0: FunTyping f ft)
        (env: valEnv)
        (k: SoundFun env (extParType ft) f (extRetType ft) n)
                   : prod (vtypExt (extRetType ft)) W := _.

Next Obligation.
  unfold SoundFun in k.
  destruct ft.
  (*simpl in m.*)
  simpl in k.
  simpl.
  destruct f.
  inversion k0; subst.  
  specialize (k eq_refl).
  eapply SOS_Exp.
  exact k.
  specialize (k eq_refl).
  eapply SOS_Exp.
  exact k.
Defined.  
  

Program Definition SOS_QFun
         (ftenv: funTC) (fenv: funEnv)
         (q: QFun) (ft: FTyp) (n: W)
         (k0: QFunTyping ftenv fenv q ft)
         (env: valEnv)  
         (k: SoundQFun fenv env (extParType ft) q (extRetType ft) n)
              : prod (vtypExt (extRetType ft)) W := _.

Next Obligation.
  unfold SoundQFun in k.
  destruct k.
  specialize (q0 n).
  eapply SOS_Fun in s.
  exact s.
  inversion k0; subst.
  inversion q0; subst.
  exact X.
  inversion X0.
  inversion q0; subst.
  inversion X0; subst.
  inversion X; subst.
  assert (findE ls1 x0 = None).
  eapply ExRelValTNone in X3.
  exact X3.
  exact ft.
  exact H.
  inversion X1; subst.
  assert (findE (overrideE ls1 ((x0, f) :: ls3)) x0 =
                 findE ((x0, f) :: ls3) x0). 
  rewrite overrideRedux2.
  auto.
  exact H0.
  unfold overrideE in H2.
  rewrite H2 in H1.
  simpl in H1.
  destruct (IdT.IdEqDec x0 x0) in H1.
  inversion H1; subst.
  exact X2.
  intuition n.
Defined.  

   
Program Fixpoint SOS_Prms
                   (fenv: funEnv) (env: valEnv)
                   (ps: Prms) (pt: PTyp) (n: W) 
                   (k: SoundPrms fenv env ps pt n) :
                              prod (PTyp_Trans pt) W := _.

Next Obligation.
  unfold SoundPrms in k.
  destruct k as [es m].
  split.
(**)  
  - destruct m as [vs m1 k].
    destruct k as [m2 k].
    inversion m2; subst.
    unfold PTyp_Trans.
    revert m1.
    revert vs.
    revert k.
    revert ps.
    revert n.
    induction X.
    + simpl.
      intros.
      exact tt.
    + intros.
      destruct vs.
      inversion m1; subst.
      simpl in H.
      inversion H.
      destruct ps.
      destruct es.
      destruct k as [n2 k].
      inversion k; subst.
      inversion X0.
      inversion m2; subst.
      inversion X0; subst.
      
      assert (PrmsTyping emptyE emptyE emptyE (PS l) (PT l')).
      * constructor.
        exact X2.
      * specialize (IHX X3).
        inversion m1; subst.
        simpl in H.
        inversion H; subst.
        clear H.
        assert (isValueList2T (map Val vs) vs) as J1.
        constructor.
        auto.
        inversion X1; subst.

        eapply PrmsClos_aux1 in k.
        destruct k.
        destruct p.
       
        constructor.
        unfold VTyp_Trans.
        eapply (SOS_Exp fenv env e y n).
        unfold SoundExp.
        constructor 1 with (x:=v).
        exact H3.
        econstructor 1 with (x:=x).
        exact e0.

        specialize (IHX x (PS es) s vs J1).
        exact IHX.
  - destruct m.
    destruct p.
    destruct s.
    exact x0.
(*  Show Proof.
  Unshelve.
  exact fenv.
  exact env.
  exact n.
*)
Defined.


  

(*
Program Definition SOS_Exp (Z: Type) (PZ: PState Z)
                   (fenv: funEnv) (env: valEnv)
                   (e: Exp) (t: VTyp) (n: Z) 
                   (k: SoundExp Z PZ fenv env e t n) (n: Z) :
                              prod (vtypExt t) Z := _.
*)
(*
Lemma InterEquivExp 
         (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (e: Exp) (t: VTyp) (k0: ExpTyping ftenv tenv fenv e t) 
         (k1: FEnvTyping fenv ftenv)   
         (env: valEnv)
         (k2: EnvTyping env tenv) (n: W) :  
         Exp_Trans ftenv tenv fenv e t k0 k1 env k2 n = 
         SOS_Exp fenv env e t n 
                 (ExpEval ftenv tenv fenv e t k0 k1 env k2 n).
Proof.
  unfold Exp_Trans.
  unfold SOS_Exp.
Admitted.


Lemma InterEquivPrms 
         (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (ps: Prms) (pt: PTyp) (k0: PrmsTyping ftenv tenv fenv ps pt) 
         (k1: FEnvTyping fenv ftenv)   
         (env: valEnv)
         (k2: EnvTyping env tenv) (n: W) :  
         Prms_Trans ftenv tenv fenv ps pt k0 k1 env k2 n = 
         SOS_Prms fenv env ps pt n 
                 (PrmsEval ftenv tenv fenv ps pt k0 k1 env k2 n).
Proof.
Admitted.


Lemma InterEquivFun 
         (f: Fun) (ft: FTyp) (k0: FunTyping f ft) 
         (env: valEnv) 
         (k1: EnvTyping env (extParType ft)) (n: W) :
         Fun_Trans f ft k0 (WT_valEnv_Trans (extParType ft) env k1) n = 
         SOS_Fun f ft n k0 env (FunEval f ft k0 env k1 n).
Proof.
Admitted.


Lemma InterEquivQFun
         (ftenv: funTC) (fenv: funEnv)
         (q: QFun) (ft: FTyp) 
         (k0: QFunTyping ftenv fenv q ft)
         (k1: FEnvTyping fenv ftenv)   
         (env: valEnv) 
         (k2: EnvTyping env (extParType ft)) (n: W) :  
  QFun_Trans ftenv fenv q ft k0 k1 
             (WT_valEnv_Trans (extParType ft) env k2) n = 
         SOS_QFun ftenv fenv q ft n k0 env   
                          (QFunEval ftenv fenv q ft k0 k1 env k2 n).
Proof.
Admitted.

*)

  

(*************************************************************************)
(*** superseded ******************)

Definition SoundFunB 
         (f: Fun) (ft: FTyp) 
         (k: FunTyping f ft)
         (env: valEnv)
         (m: EnvTyping env (extParType ft)) (n: W) :=
  SoundFun env (extParType ft) f (extRetType ft) n. 
  
Program Definition SOS_FunB
        (f: Fun) (ft: FTyp) (n: W)
        (k0: FunTyping f ft)
        (env: valEnv)
        (m: EnvTyping env (extParType ft)) 
        (k: SoundFunB f ft k0 env m n)
                   : prod (vtypExt (extRetType ft)) W := _.

Next Obligation.
  unfold SoundFunB in k.
  destruct ft.
  simpl in m.
  simpl in k.
  simpl.
  unfold SoundFun in k.
  destruct f.
  inversion k0; subst.  
  specialize (k eq_refl).
  eapply SOS_Exp.
  exact k.
  specialize (k eq_refl).
  eapply SOS_Exp.
  exact k.
Defined.  

(*************)

Definition SoundFunC
         (f: Fun) (ft: FTyp) (n: W)
         (k: FunTyping f ft)
         (env: valEnv) :=
         (* EnvTyping env (extParType ft) -> *)
  SoundFun env (extParType ft) f (extRetType ft) n. 


Definition SoundQFunC
         (ftenv: funTC) (fenv: funEnv)
         (q: QFun) (ft: FTyp) (n: W)
         (k: QFunTyping ftenv fenv q ft)
         (env: valEnv) :=
(*         EnvTyping env (extParType ft) ->  *)
  SoundQFun fenv env (extParType ft) q (extRetType ft) n. 



End SOS2Gall.