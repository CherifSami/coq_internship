
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
Require Import IdModType.

Module TSoundness (IdT: IdModType) <: IdModType.
(* Export IdT. *)

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module WeakeningC := Weakening IdT.
Export WeakeningC.
 

Definition SoundExpA (fenv: funEnv) (env: valEnv)
                     (e: Exp) (t: VTyp) (n: W)  
  := sigT2 (fun v: Value => ValueTyping v t)
           (fun v: Value => sigT (fun n': W =>
                         EClosure fenv env (Conf Exp n e)
                                                (Conf Exp n' (Val v)))).


Definition Par_F := fun (f: Fun) (ft: FTyp) 
                         (k: FunTyping f ft) =>
    forall (fps: valTC) (t: VTyp),
    ft = FT fps t ->      
    forall (i: nat) (fenv': funEnv) 
           (x: Id) (e0 e1: Exp), 
       f = FC fenv' fps e0 e1 x i -> 
       forall (n: W) (env: valEnv), 
       EnvTyping env fps -> 
       match i with 
         | 0 => SoundExpA fenv' env e0 t n
         | S j => SoundExpA (updateE fenv' x (FC fenv' fps e0 e1 x j))
                           env e1 t n
       end.


Definition Par_F_Mod := fun (f: Fun) (ft: FTyp) 
                         (k: FunTyping f ft) =>
    forall env: valEnv, 
       EnvTyping env (extParType ft) -> 
    forall n: W, 
    forall (fenv': funEnv) (e0 e1: Exp)
           (x: Id) (i: nat),
      let fps := extParType ft in
      let t := extRetType ft in 
       f = FC fenv' fps e0 e1 x i -> 
       match i with 
         | 0 => SoundExpA fenv' env e0 t n
         | S j => SoundExpA (updateE fenv' x (FC fenv' fps e0 e1 x j))
                           env e1 t n
       end.



Definition Par_Q := fun (ftenv: funTC) (fenv: funEnv)
                         (q: QFun) (ft: FTyp) 
                         (k: QFunTyping ftenv fenv q ft) =>
   FEnvTyping fenv ftenv -> 
   forall n: W,
     sigT2 (fun f: Fun =>
                  sigT (fun k1: FunTyping f ft => Par_F f ft k1))
           (fun f: Fun => QFClosure fenv (Conf QFun n q)
                                           (Conf QFun n (QF f))).


Definition Par_E :=
     fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                        (e: Exp) (t: VTyp) 
                        (k: ExpTyping ftenv tenv fenv e t) =>
  FEnvTyping fenv ftenv ->
  forall env: valEnv,                      
  EnvTyping env tenv ->
  forall n: W, SoundExpA fenv env e t n.


Definition Par_P :=
      fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                         (ps: Prms) (pt: PTyp) 
                         (k: PrmsTyping ftenv tenv fenv ps pt) => 
  FEnvTyping fenv ftenv ->
  forall env: valEnv,                      
  EnvTyping env tenv ->
  forall n: W, 
      sigT (fun es: list Exp =>
        sigT2 (isValueList2T es) 
              (fun vs: list Value =>
                 prod (PrmsTyping emptyE emptyE emptyE (PS es) pt)
                      (sigT (fun n': W =>
                         PrmsClosure fenv env (Conf Prms n ps)
                                                   (Conf Prms n' (PS es)))))).


Definition ExpTypingSoundA_rect :=
  ExpTyping_str_rect
           Par_F Par_Q Par_E Par_P. 


Lemma WellTypedEvalM :
  forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (e: Exp) (t: VTyp),
      ExpTyping ftenv tenv fenv e t ->
      FEnvTyping fenv ftenv ->
      forall env: valEnv,                      
      EnvTyping env tenv ->
      forall n: W, SoundExpA fenv env e t n.

Proof.
eapply ExpTypingSoundA_rect.

- (** base Par_SSL *)
  unfold Par_SSL, Par_E.
  constructor.

- (** step Par_SSL *)
  unfold Par_SSL, Par_E.
  intros.  
  constructor.
  + assumption.
  + assumption.    
  + assumption.

- (** base Par_SSA *)
  unfold Par_SSA, Par_F.
  constructor.

- (** step Par_SSA *)
  unfold Par_SSA, Par_F.
  intros.
  constructor.
  + assumption.
  + assumption.
  + assumption.

- (** Par_SSB *)
  unfold Par_SSB, Par_SSA, Par_F.
  intros.
  eapply (Forall2BT_split FunTyping _ _ 
                         fenv fenv0 fenv1 ftenv ftenv0 ftenv1 x f t).
  + assumption.
  + assumption.
  + assumption.
  + assumption.
  + assumption.
  + assumption.
  + assumption.  
  + assumption.

- (** base Par_F *)
  unfold Par_F, Par_E.
  intros.
  inversion H; subst.
  inversion H0; subst.
  specialize (X m env X0 n).
  assumption.

- (** step Par_F *)
  unfold Par_F, Par_E.
  intros.
  inversion H; subst.
  inversion H0; subst.  
  rename n into i.
  rename fenv'0 into fenv.
  eapply updateFEnvLemma with (x:= x0)
              (v1:= FC fenv fps e2 e3 x0 i) (v2:= FT fps t0) in m.
  specialize (X m env X1 n0).
  assumption.
  assumption.

- (** Par_Q - QF *)    
  unfold Par_Q, Par_F.
  intros.
  constructor 1 with (x:=f).
  * constructor. 
    assumption.
    assumption.
  * constructor.  
    
- (** Par_Q - FId *)
  unfold Par_Q, Par_SSB, Par_F, Par_SSA.
  intros.
  inversion X; subst.
  clear X. 
  constructor 1 with (x:=f).
  + constructor.
    assumption.
    assumption.
  + constructor.
    constructor.
    constructor.
    clear X1 X2 X3.
    inversion m; subst.
    rewrite H0.
    eapply ExRelValTNone with (venv:=ls1) in H.
    * eapply findEexApp with (env:=(x,f)::ls3) in H.
      rewrite <- H at 1.
      simpl.
      destruct (IdT.IdEqDec x x).
      {- auto. }
      {- intuition n0. }
    * auto.
    * eauto.
(** Par_E *)
-  (* modify *)
  unfold Par_E, SoundExpA.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q H H0 env H0' n.
  inversion H; subst.
  destruct v.
  destruct v.
  inversion H1; subst.
  subst T.
  simpl in H2.
  destruct H2.
  constructor 1 with (x:=cst T2 (b_eval _ _ XF n v)).
  + constructor.
    * reflexivity.
    * constructor.  
  + inversion H; subst.
    * inversion H1; subst.
      subst T.
      simpl in H2.
      clear H2.
      constructor 1 with (x:=b_exec _ _ XF n v).
      eapply StepIsEClos.
      constructor.
  + inversion X; subst.
    eapply ExTDefNatT with (venv:=env) (T:=T1) in X0.      
    * destruct X0 as [v k].
      constructor 1 with (x:= cst T2 (b_eval _ _ XF n v)).
      econstructor.
      {- constructor. }
      {- econstructor. }
      {- constructor 1 with (x:=b_exec _ _ XF n v). 
         econstructor.
         econstructor.
         econstructor.
         eassumption.
         eapply StepIsEClos.
         constructor. }
    * assumption.
    * assumption.
    * reflexivity.
- (* return *)
  unfold Par_E, SoundExpA.
  intros G ftenv tenv fenv q t H H0 env H0' n.
  inversion H; subst.
  + constructor 1 with (x:=v).
    * assumption.
    * constructor 1 with (x:=n).
      econstructor.
      {- econstructor. }
      {- constructor. }
  + inversion X; subst.
    eapply ExTDefVal with (venv:=env) in X0.     
    * destruct X0 as [v k1 k2].
      constructor 1 with (x:=v).
      {- assumption. }
      {- constructor 1 with (x:=n).
         econstructor. 
         + constructor.
           constructor.
           eassumption.             
         + eapply StepIsEClos.
           constructor.
      }
    * auto.   
- (* bindN *)
  unfold Par_E, SoundExpA.
  intros ftenv tenv fenv e1 e2 t1 t2.
  intros k1 k2 IH1 IH2.
  intros H0 env H0' n.  
  specialize (IH1 H0 env H0' n).
  destruct IH1 as [v0 k3 H2].
  destruct H2 as [n0 H2].
  specialize (IH2 H0 env H0' n0).
  destruct IH2 as [v2 k4 H3].
  destruct H3 as [n2 H3].
  constructor 1 with (x:=v2).
  + auto.
  + constructor 1 with (x:=n2).
    eapply (EClosConcat fenv env).
    * instantiate  (1 := Conf Exp n0 (BindN (Val v0) e2)).
      apply  BindN_extended_congruence.
      assumption.
    * econstructor.
      {- econstructor. }
      {- assumption. }
- (* BindS *)
  unfold Par_E, SoundExpA.
  intros ftenv tenv tenv' fenv x e1 e2 t1 t2.
  intros H k1 k2 IH1 IH2.
  intros H0 env H0' n.  
  specialize (IH1 H0 env H0' n).
  destruct IH1 as [v1 k3 H1].
  destruct H1 as [n0 H1].
  specialize (IH2 H0 (updateE env x v1)).
  cut (EnvTyping (updateE env x v1) (updateE tenv x t1)).
  + intro.
    rewrite H in IH2.
    specialize (IH2 X n0).
    destruct IH2 as [v2 k4 H2].
    destruct H2 as [n1 H2].
    constructor 1 with (x:=v2).
    * assumption.   
    * constructor 1 with (x:=n1).    
      eapply EClosConcat.
      {- instantiate (1:= (Conf Exp n0 (BindS x (Val v1) e2))).
         apply BindS_extended_congruence.
         assumption.
      }   
      {- eapply EClosConcat.
         + eapply StepIsEClos.
           econstructor.
         + eapply EClosConcat.
           * eapply BindMS_extended_congruence.
             {- reflexivity. }
             {- reflexivity. }
             {- unfold overrideE. 
                rewrite app_nil_l.
                eassumption.
             }
           * eapply StepIsEClos.
             constructor.
       }      
  + apply updateVEnvLemma.  
    * assumption.
    * assumption.
- (* BindMS *)
  unfold Par_E, SoundExpA.  
  intros ftenv ftenvP ftenv' tenv tenvP tenv' fenv fenvP fenv' envP e t.
  intros k1 k2 k3 E1 E2 E3 k4 IH.  
  intros H0 env H0' n.
  eapply (overrideVEnvLemma envP env tenvP tenv k1) in H0'.
  eapply (overrideFEnvLemma fenvP fenv ftenvP ftenv k3) in H0.
  cut (FEnvTyping fenv' ftenv').
  + cut (EnvTyping (overrideE envP env) tenv').
    * intros H1' H1.
      specialize (IH H1 (overrideE envP env) H1' n). 
      destruct IH as [v k5 H2].
      destruct H2 as [n1 H2].
      constructor 1 with (x:=v).
      {- auto. }
      {- constructor 1 with (x:=n1).
         eapply (EClosConcat fenv env).
         + eapply BindMS_extended_congruence.
           * reflexivity.
           * reflexivity.
           * rewrite <- E3. 
             eassumption.
         + eapply StepIsEClos.
           constructor.
      }    
    * rewrite E1.
      assumption.
  + rewrite E2.
    rewrite E3.
    assumption.
- (* Apply *)
  unfold Par_Q, Par_P, Par_E, SoundExpA.  
  intros ftenv tenv fps fenv q ps pt t.  
  intros E1 k1 k2 k3 IH1 IH2.
  intros H0 env H0' n.

  cut (sigT (fun n' : W =>
        (sigT (fun f: Fun =>
          sigT2 (fun es: list Exp => isValueListT es)
             (fun es: list Exp => prod
               (EClosure fenv env (Conf Exp n (Apply q ps))
                         (Conf Exp n' (Apply (QF f) (PS es))))
               (sigT2 (fun v : Value =>
                    sigT (fun n'' : W =>                  
                       EClosure fenv env
                             (Conf Exp n' (Apply (QF f) (PS es)))
                             (Conf Exp n'' (Val v)))) 
                    (fun v: Value => ValueTyping v t))))))).

  intros.
  + destruct X as [n1 X].
    destruct X as [f X].
    destruct X as [vls k4 X].
    destruct X as [H1 X].
    destruct X as [v X k5].   
    destruct X as [n2 H2].
    constructor 1 with (x:=v).
    * assumption.
    * constructor 1 with (x:=n2). 
      eapply EClosConcat.
      {- eassumption. }
      {- eassumption. }
  + specialize (IH1 H0 n). 
    destruct IH1 as [f H3 H1].
    destruct H3 as [k5 HF].
    (* destruct H1 as [n1 H1]. *)
    specialize (IH2 H0 env H0' n). 
    destruct IH2 as [es H2].
    destruct H2 as [vs k6 H2].
    destruct H2 as [k7 H2].
    destruct H2 as [n1 H2].
    constructor 1 with (x:=n1).
    constructor 1 with (x:=f).
    constructor 1 with (x:=es).
    * eapply isValueList2IsValueT.
      eassumption.
    * destruct pt.
      inversion E1; subst.
      split.
      {- eapply EClosConcat.  
         + instantiate (1:=(Conf Exp n (Apply (QF f) ps))).
           eapply Apply2_extended_congruence. 
           assumption.
         + eapply Apply1_extended_congruence.
           assumption.
      }   
      {- eapply matchListsAux02_T with (vs:=vs) in k7.
         assert (length fps = length vs) as H5.
         + eapply prmsAux2.
           * eassumption.
         + unfold Par_F in HF.
           specialize (HF fps t eq_refl).
           eapply prmsTypingAux_T in k7.
           inversion k5; subst.
           * specialize (HF 0 fenv0 x e0 e1 eq_refl).
             specialize (HF n1 (mkVEnv fps vs)).
             {- specialize (HF k7).
                destruct HF as [v k8 HF].
                destruct HF as [n2 HF].
                constructor 1 with (x:=v).
                + constructor 1 with (x:=n2).
                  econstructor.
                  * eapply Apply_EStep0.
                    {- eassumption. }
                    {- assumption. }
                    {- reflexivity. }
                  * eapply EClosConcat.
                    {- eapply BindMS_extended_congruence.
                       + reflexivity.
                       + reflexivity.
                       + eapply (weak fenv0 fenv (mkVEnv fps vs) env)
                                in HF.
                         eassumption.
                    }     
                    {- apply StepIsEClos.
                       constructor.
                    }   
                + assumption.
             }
           * specialize (HF (S n0) fenv0 x e0 e1 eq_refl).
             specialize (HF n1 (mkVEnv fps vs)). 
             {- specialize (HF k7).
                destruct HF as [v k8 HF].
                destruct HF as [n2 HF].
                constructor 1 with (x:=v).
                + constructor 1 with (x:=n2).
                  econstructor.
                  * eapply Apply_EStep1.
                    {- eassumption. }
                    {- assumption. }
                    {- reflexivity. }
                  * eapply EClosConcat.
                    {- eapply BindMS_extended_congruence.
                       + reflexivity.
                       + reflexivity.
                       + eapply weak.
                         eassumption.
                    }     
                    {- apply StepIsEClos.
                       constructor.
                    }         
                + assumption.
             }
          * assumption.
        + assumption.
      }  
- (* Val *)
  unfold Par_E, SoundExpA.
  intros.
  constructor 1 with (x:=v).
  + assumption.
  + constructor 1 with (x:=n).
    constructor.
- (* IFThenElse *)
  unfold Par_E, SoundExpA.    
  intros.
  specialize (X X2 env X3 n).
  destruct X as [v K X].
  destruct X as [n' X].
  specialize (X0 X2 env X3 n').
  destruct X0 as [v0 K0 X0].
  destruct X0 as [n0 X0].
  specialize (X1 X2 env X3 n').
  destruct X1 as [v1 K1 X1].
  destruct X1 as [n1 X1].
  inversion K; subst.
  subst T.
  destruct v as [T v].
  destruct v.
  
  unfold Bool in H.
  unfold vtyp in H.
  simpl in H.
  inversion H; subst.
 
  destruct v.
  + constructor 1 with (x:=v0).
    assumption.
    constructor 1 with (x:=n0).
    eapply EClosConcat.
    instantiate (1:=Conf Exp n'
       (IfThenElse (Val (existT ValueI bool (Cst bool true))) e2 e3)).
    eapply IfThenElse_extended_congruence.
    eassumption.

    econstructor.
    econstructor.

    eassumption.
(*
    eapply IfThenElse_extended_congruence.
    exact X.
    econstructor.
    constructor.
    assumption.
*)    
  + constructor 1 with (x:=v1).
    assumption.
    constructor 1 with (x:=n1).
    eapply EClosConcat.
    eapply IfThenElse_extended_congruence.
    eassumption.
    econstructor.
    econstructor.
    eassumption.
- (** Par_P *)
  unfold Par_SSL, Par_E, Par_P, SoundExpA.
  intros.
  dependent induction X.
  constructor 1 with (x:=nil).
  constructor 1 with (x:=nil).
  constructor.
  simpl.
  auto.
  split.
  constructor.
  constructor.
  constructor 1 with (x:=n).
  constructor.
  (**)
  clear X.
  specialize (p0 X0 env X1 n).
  destruct p0 as [v k1 X2].
  destruct X2 as [n1 H].
  inversion m; subst.
  specialize (IHX X2).
  specialize (IHX X0 env X1 n1).
  destruct IHX as [es IHX].
  destruct IHX as [vs k2 IHX].
  destruct IHX as [k3 IHX].
  destruct IHX as [n2 k4].
  constructor 1 with (x:=(Val v::es)).
  constructor 1 with (x:=v::vs).
  constructor.
  eapply IsValueList2T.
  simpl.
  inversion k2; subst.
  auto.
  split.
  constructor.
  constructor.
  constructor.
  assumption.
  inversion k3; subst.
  assumption.
  constructor 1 with (x:=n2).
  eapply PrmsConcat.
  eapply Pars_extended_congruence2.
  eassumption.  
  eapply Pars_extended_congruence1.  
  assumption.
Defined.
  
End TSoundness.
