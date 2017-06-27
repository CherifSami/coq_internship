Require Import Arith List.
Import List.ListNotations.
Require Import Eqdep FunctionalExtensionality Coq.Program.Tactics.
Require Import Coq.Init.Specif.
Require Import Coq.Logic.JMeq.

Require Import TPipStaticM2.
Require Import TRInductM2.
Require Import DetermM2.
(* Require Import Test3. *)

Module Reflect (IdT: IdModType) <: IdModType.
(* Export IdT. *)

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module DeterminismC := Determinism IdT.
Export DeterminismC.

Definition MM (S A : Type) : Type := S -> A * S.

Definition ret {S A : Type} (a : A) : MM S A :=
  fun s => (a , s).

Definition bind {S A B : Type} (m : MM S A)(f : A -> MM S B) : MM S B :=  
fun s => match m s with
    | (a, s') => f a s'
    end.

(*************************************************************************)

Definition VTyp_Trans (t: VTyp) : Type :=
  vtypExt t.

Definition PTyp1_Trans (pt: PTyp) : list Type :=
  match pt with
      PT ts => map vtypExt ts
  end.                 

Fixpoint TList_Trans (ts: list VTyp) : Type :=
  match ts with
      | nil => unit
      | (t::ts') => (VTyp_Trans t) * (TList_Trans ts')
  end.                                    

Definition valTC_Trans (tenv: valTC) : Type := TList_Trans (map snd tenv).

(*
Fixpoint valTC_Trans (tenv: valTC) : Type :=
  match tenv with
      | nil => unit
      | (t::ts) => (VTyp_Trans (snd t)) * (valTC_Trans ts)
  end.                                    
*)

Definition PTyp_Trans (pt: PTyp) : Type :=
  match pt with
      PT ts => TList_Trans ts
  end.                 

Fixpoint tlist2type (ts: list Type) : Type :=
  match ts with
    | nil => unit
    | (t::ts') => t * tlist2type ts'
  end.                               

Inductive IsTypeList1 : list Type -> Type :=
  | IsTLN1 : IsTypeList1 nil
  | IsTLC1 : forall (ts: list Type) (t: Type),
              IsTypeList1 ts -> IsTypeList1 (t::ts).


Program Fixpoint listTypTrA (xts: list Type) (ps : tlist2type xts) :
  list Value := _.

Next Obligation.
  dependent induction xts.
  exact nil.
  inversion ps; subst.
  apply IHxts in X0.
  exact (cst a X::X0).
(*  Show Proof. *)
Defined.  

Program Fixpoint listTypTrB (xts: list VTyp) (ps : TList_Trans xts) :
  list Value := _.

Next Obligation.
  dependent induction xts.
  exact nil.
  inversion ps; subst.
  apply IHxts in X0.
  exact (cst (VTyp_Trans a) X::X0).
Defined.  

Program Fixpoint listTypTr (xts: list VTyp) (ps : TList_Trans xts) :
  list Value := _.

Next Obligation.
  revert ps.
  induction xts.
  intros.
  exact nil.
  intros.
  simple inversion ps; subst.
  intros.
  apply IHxts in X0.
  exact (cst (VTyp_Trans a) X::X0).
Defined.  


Lemma listTypTrL1 (t: VTyp) (ts: list VTyp)
                   (v: VTyp_Trans t) (pv: TList_Trans ts) :
  listTypTr (t::ts) (v,pv) = (cst (vtypExt t) v) :: (listTypTr ts pv).

unfold VTyp_Trans in v.
unfold vtypExt in v.
unfold vtypExt.
simpl.
unfold VTyp_Trans.
unfold vtypExt.
simpl.
cut (listTypTr_obligation_1 ts pv = listTypTr ts pv).
intros.
rewrite H.
reflexivity.
revert pv.
induction ts.
intros.
reflexivity.
intros.
simpl.
reflexivity.
Defined.


Inductive IsTypeList : list Type -> list Value -> Type :=
  | IsTLN : IsTypeList nil nil
  | IsTLC : forall (ts: list Type) (vs: list Value) (t: Type) (v: t),
              IsTypeList ts vs -> IsTypeList (t::ts) (cst t v::vs).


Definition valTC2_Trans (tenv: valTC) : list (Id * Type) :=
  map (fun (x: Id * VTyp) => (fst x, VTyp_Trans (snd x))) tenv.

Definition valTC1_Trans (tenv: valTC) : list Type :=
  map (fun (x: Id * VTyp) => (VTyp_Trans (snd x))) tenv.

Fixpoint valTC_TransA (tenv: valTC) : Type :=
  match tenv with
      | nil => unit
      | (t::ts) => (VTyp_Trans (snd t)) * (valTC_TransA ts)
  end.                                    
  
Definition FTyp_Trans1 (ft: FTyp) : Type :=
  match ft with
    | FT tenv t => valTC_Trans tenv -> MM W (VTyp_Trans t)
  end.                                                

Definition FTyp_Trans (ft: FTyp) : Type :=
   valTC_Trans (extParType ft) -> MM W (VTyp_Trans (extRetType ft)).                                                
Definition funTC2_Trans (tenv: funTC) : list (Id * Type) :=
  map (fun (x: Id * FTyp) => (fst x, FTyp_Trans (snd x))) tenv.

Definition funTC1_Trans (tenv: funTC) : list Type :=
  map (fun (x: Id * FTyp) => (FTyp_Trans (snd x))) tenv.

Fixpoint funTC_Trans (tenv: funTC) : Type :=
  match tenv with
      | nil => unit
      | (t::ts) => (FTyp_Trans (snd t)) * (funTC_Trans ts)
  end.                                    

Definition Value_Trans (v: Value) :  projT1 v := cstExt v.

(*********************)

Definition valTyp (v: Value) : Type := projT1 v.

Definition vList_Typ_Trans (ls: list Value) : Type :=
      tlist2type (map valTyp ls).

Program Fixpoint vList_Trans (ls: list Value) : vList_Typ_Trans ls
        (*  tlist2type (map valTyp ls) *)
  := _.
Next Obligation.
  induction ls.
  simpl.
  exact tt.
  simpl.
  split.
  exact (Value_Trans a).
  exact IHls.
Defined.  


Definition valEnv_Typ_Trans (env: valEnv) : Type :=
    vList_Typ_Trans (map snd env).

Definition valEnv_Trans (env: valEnv) : 
  valEnv_Typ_Trans env := vList_Trans (map snd env).

Lemma WT_Value_Trans (v: Value) (t: VTyp) :
   ValueTyping v t -> valTyp v = VTyp_Trans t.
  intros.
  inversion H; subst.
  unfold valTyp.
  unfold VTyp_Trans.
  unfold vtypExt.
  auto.
Defined.
    
Lemma WT_valEnv_Trans_eq (tenv: valTC) (env: valEnv) :
  EnvTyping env tenv -> 
              valTC_Trans tenv = valEnv_Typ_Trans env.
  intros.
  dependent induction X.  
  compute.
  reflexivity.
  assert (valTC_Trans ((k, v2) :: ls2) =
          prod (VTyp_Trans v2) (valTC_Trans ls2)).  
  reflexivity.
  assert (valEnv_Typ_Trans ((k, v1) :: ls1) =
          prod (valTyp v1) (valEnv_Typ_Trans ls1)).
  reflexivity.
  rewrite H.
  rewrite H0.
  rewrite IHX.
  eapply WT_Value_Trans in r.
  rewrite r.
  auto.
Defined.  

Lemma WT_valEnv_Trans (tenv: valTC) (env: valEnv) :
  EnvTyping env tenv -> valTC_Trans tenv.
intros.
assert (valEnv_Typ_Trans env).
exact (valEnv_Trans env).
rewrite (WT_valEnv_Trans_eq tenv env).
exact X0.
exact X.
Defined.

  
(**********************)

Definition E_Trans0 :=
    fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
          (e: Exp) (t: VTyp) (ET: ExpTyping ftenv tenv fenv e t) => 
        MM W (VTyp_Trans t).

Definition F_Trans0 := fun (f: Fun) (ft: FTyp)
               (ET: FunTyping f ft) => FTyp_Trans ft.

Definition Q_Trans0 :=
    fun (ftenv: funTC) (fenv: funEnv) (q: QFun) (ft: FTyp) 
                (ET: QFunTyping ftenv fenv q ft) => 
                        FTyp_Trans ft.

Definition P_Trans0 :=
    fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                (ps: Prms) (ts: PTyp) 
                (ET: PrmsTyping ftenv tenv fenv ps ts) => 
       MM W (PTyp_Trans ts).


Definition ExpTypingTrans0_rect :=
  ExpTyping_str_rect 
           F_Trans0 Q_Trans0 E_Trans0 P_Trans0. 


(************************************)


Definition E_Trans :=
  fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
          (e: Exp) (t: VTyp) (ET: ExpTyping ftenv tenv fenv e t) => 
  FEnvTyping fenv ftenv ->   
  forall env: valEnv,
        EnvTyping env tenv -> 
        MM W (VTyp_Trans t).


Definition F_Trans :=
  fun (f: Fun) (ft: FTyp)
               (FT: FunTyping f ft) => 
 (* forall env: valEnv,
       EnvTyping env (extParType ft) -> *)     
       FTyp_Trans ft. 
                        

Definition Q_Trans :=
  fun (ftenv: funTC) (fenv: funEnv) (q: QFun) (ft: FTyp) 
                          (QT: QFunTyping ftenv fenv q ft) =>
  FEnvTyping fenv ftenv ->          
(*  forall env: valEnv,
       EnvTyping env (extParType ft) ->  *)    
       FTyp_Trans ft. 


Definition P_Trans :=
  fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                (ps: Prms) (ts: PTyp) 
                (ET: PrmsTyping ftenv tenv fenv ps ts) => 
  FEnvTyping fenv ftenv ->   
  forall env: valEnv,
        EnvTyping env tenv -> 
        MM W (PTyp_Trans ts).



Definition ExpTypingTrans_rect :=
  ExpTyping_str_rect 
           F_Trans Q_Trans E_Trans P_Trans. 


Definition FunTypingTrans_rect :=
  ExpTypingF_str_rect 
           F_Trans Q_Trans E_Trans P_Trans. 


Definition ParTypingTrans_rect :=
  ExpTypingP_str_rect  
           F_Trans Q_Trans E_Trans P_Trans. 


Definition QFunTypingTrans_rect :=
  ExpTypingQ_str_rect 
           F_Trans Q_Trans E_Trans P_Trans. 


Lemma envTypingListTT (fps : valTC) (t0 : TList_Trans (map snd fps)):
  EnvTyping (mkVEnv fps (listTypTr (map snd fps) t0)) fps.
Proof.
    unfold mkVEnv.          
    dependent induction fps.
    constructor.
    destruct a.
    rewrite map_cons.
    
    assert (listTypTr (map snd ((i, v) :: fps)) t0 =
            listTypTr (snd (i, v) :: (map snd fps)) t0). 
    simpl.
    reflexivity.

    rewrite H.

    assert (listTypTr (snd (i, v) :: (map snd fps)) t0 =
            listTypTr (v :: (map snd fps)) t0).
    simpl.
    reflexivity.
    
    rewrite H0 at 1.
    
    assert (fst (i,v) = i).
    auto.
    
    rewrite H1.
    
    destruct t0.

    rewrite listTypTrL1.

    simpl.
    constructor.
    constructor.
    simpl.
    reflexivity.
    simpl.
    constructor.

    assert (EnvTyping (interleave (map fst fps)
                                  (listTypTr (map snd fps) t)) fps).
    eapply IHfps.
    unfold EnvTyping in X.
    exact X.
Defined.
    


Program Fixpoint Exp_Trans 
        (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (e: Exp) (t: VTyp) (ET: ExpTyping ftenv tenv fenv e t) :
  FEnvTyping fenv ftenv ->   
  forall env: valEnv,
        EnvTyping env tenv -> 
        MM W (VTyp_Trans t) := _ 
with Fun_Trans 
               (f: Fun) (ft: FTyp) 
               (ET: FunTyping f ft) :
(*  forall env: valEnv,
       EnvTyping env (extParType ft) ->  *)     
       FTyp_Trans ft := _ 
with QFun_Trans 
                (ftenv: funTC) (fenv: funEnv) (q: QFun) (ft: FTyp)
                (ET: QFunTyping ftenv fenv q ft) :
  FEnvTyping fenv ftenv ->          
(*  forall env: valEnv,
       EnvTyping env (extParType ft) ->  *)    
       FTyp_Trans ft := _ 
with Prms_Trans 
                (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                (ps: Prms) (ts: PTyp) 
                (ET: PrmsTyping ftenv tenv fenv ps ts) :
  FEnvTyping fenv ftenv ->   
  forall env: valEnv,
        EnvTyping env tenv -> 
        MM W (PTyp_Trans ts) := _.
 
Next Obligation.
  
  revert X0.
  revert env.
  revert X.
  revert ET.
  revert e t.
  eapply ExpTypingTrans_rect.
  
  - (* forall2_nil *)
    unfold Par_SSL.
    intros.
    constructor.
  - (* forall2_cons *)
    unfold Par_SSL.
    intros.
    econstructor.
    exact X0.
    exact X.  
  - (* matchenvs_nil *)
    unfold Par_SSA.
    constructor.
  - (* matchenvs_cons *)
    unfold Par_SSA.
    intros.
    econstructor.
    exact X0.
    exact X.    
  - (* matchenvs2_split *)
    unfold Par_SSB, Par_SSA.
    intros.
    econstructor.
    exact m0.
    exact m1.
    assumption.
    assumption.
    exact X.
    exact X0.
    exact X1.
  - (* funz *) 
    unfold E_Trans, F_Trans.  
    unfold FTyp_Trans.
    intros.
    specialize (X m).
    unfold valTC_Trans in X0.
    assert (EnvTyping (mkVEnv tenv0 (listTypTr (map snd tenv0) X0)) tenv0).
    + apply envTypingListTT.
    + apply X in X1.
      exact X1.
  - (* funs *)
    unfold E_Trans, F_Trans.
    intros.
    unfold FTyp_Trans.
    intros.
    assert (FEnvTyping fenv' ftenv').
    + rewrite h1.
      rewrite h2.
      eapply updateFEnvLemma.
      exact m.
      exact k2.
    + specialize (X X2).
      (* unfold FTyp_Trans in X0. *)      
      unfold valTC_Trans in X1. 
      assert (EnvTyping (mkVEnv tenv0 (listTypTr (map snd tenv0) X1)) tenv0).
      * apply envTypingListTT.
      * apply X in X3.
        exact X3.
  - (* QF *)
    unfold Q_Trans, F_Trans.
    intros.
    exact X.
  - (* FVar *)
    unfold Par_SSB, Q_Trans, F_Trans.
    intros.
    destruct ft.
    inversion X; subst; clear X.
    exact X3.
  - (* modify *)
    unfold E_Trans.
    intros.
    simpl.
    destruct XF.
    unfold MM.
    inversion k; subst.
    + inversion H; subst.
      subst T.
      simpl in H0.
      destruct v.
      destruct v.
      simpl in H0.
      clear k.
      clear H.
      clear H1.
      rewrite H0 in v.
      intros.
      exact (b_eval0 X1 v, b_exec0 X1 v). 
    + inversion X1; subst.
      eapply ExRelValT with (x0:=x) (t:=vtyp T1) in X0.
      destruct X0.
      destruct x0.
      destruct v0.
      inversion v; subst.
      subst T.
      simpl in H.
      clear f.
      clear v.
      clear H0.
      rewrite H in v0. 
      intros.
      exact (b_eval0 X0 v0, b_exec0 X0 v0). 
      exact X2. 
  - (* return *)
    unfold E_Trans.
    intros.
    simpl.
    inversion k; subst.  
    + inversion H; subst.
      subst T. 
      destruct v.    
      destruct v.
      simpl in H0.
      unfold VTyp_Trans.
      unfold vtypExt.
      clear k H H1.
      rewrite H0 in v.    
      exact (ret v).
    + inversion X1; subst.
      eapply ExRelValT with (x0:=x) (t0:=t) in X0.
      destruct X0.
      destruct x0.
      destruct v0.      
      inversion v; subst.
      subst T.
      simpl in H.
      clear f v H0.
      rewrite H in v0.   
      exact (ret v0).
      exact X2.
  - (* bindn *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X1 env X2).
    specialize (X0 X1 env X2).
    exact (bind X (fun _ => X0)).
  - (* binds *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X1 env X2).
    specialize (X0 X1).
    unfold MM.
    intros.
(**)
    unfold MM in X.
    apply X in X3.
    destruct X3.
    eapply (updateVEnvLemma env tenv0 x
                            (cst (VTyp_Trans t1) v) t1) in X2.
    specialize (X0 (updateE env x (cst (VTyp_Trans t1) v))).
    rewrite h in X0.
    apply X0 in X2.
    apply (X2 w).
    unfold VTyp_Trans.
    unfold vtypExt.
    constructor.
    simpl.
    reflexivity.
    constructor.
  - (* bindms *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (overrideFEnvLemma
                                  fenvP fenv0 ftenvP ftenv0 m2 X0).  
    intro.
    rewrite h2 in X.
    rewrite h3 in X.
    specialize (X X2).
    specialize (overrideVEnvLemma envP env tenvP tenv0 k1 X1).
    intros.
    rewrite h1 in X.
    apply X in X3.
    exact X3.
  - (* apply *)
    unfold E_Trans, Q_Trans, P_Trans.
    intros.
    specialize (X X1).
    specialize (X0 X1 env X2).     
    simpl in X.
    inversion k2; subst.
    unfold env2ptyp in H3.
    inversion H3; subst. 
    simpl in X0.
    unfold MM; intros.
    unfold MM in X0.
    specialize (X0 X4); clear X4.
    destruct X0.
    clear H3.
    specialize (X t0).
    
    unfold MM in X.
    apply (X w).    

  - (* val *)
    unfold E_Trans.
    intros.
    simpl.
    unfold VTyp_Trans.
    unfold vtypExt.
    inversion k.
    subst T.
    rewrite <- H.
    exact (ret (cstExt v)).
  - (* ifthenelse *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X2 env X3).
    specialize (X0 X2 env X3).
    specialize (X1 X2 env X3).
    
    unfold MM; intro.
    unfold MM in X.
    specialize (X X4).
    destruct X.
    simpl in v.
    destruct v.
    exact (X0 w).
    exact (X1 w).
  - (* PS *)
    unfold Par_SSL, P_Trans.
    unfold E_Trans.
    intros.
    simpl.
    induction X.
    simpl.
    exact (ret tt).
    simpl.
    specialize (p0 X0 env X1).
    inversion m; subst.
    specialize (IHX X3).
    unfold MM; intro.
    specialize (p0 X4).
    destruct p0.
    specialize (IHX w).
    destruct IHX.
    exact (v, t, w0).
Defined.    
    
Next Obligation.
  
  revert ET.
  revert f ft.
  eapply FunTypingTrans_rect.

  - (* forall2_nil *)
    unfold Par_SSL.
    intros.
    constructor.
  - (* forall2_cons *)
    unfold Par_SSL.
    intros.
    econstructor.
    exact X0.
    exact X.  
  - (* matchenvs_nil *)
    unfold Par_SSA.
    constructor.
  - (* matchenvs_cons *)
    unfold Par_SSA.
    intros.
    econstructor.
    exact X0.
    exact X.    
  - (* matchenvs2_split *)
    unfold Par_SSB, Par_SSA.
    intros.
    econstructor.
    exact m0.
    exact m1.
    assumption.
    assumption.
    exact X.
    exact X0.
    exact X1.
  - (* funz *) 
    unfold E_Trans, F_Trans.  
    unfold FTyp_Trans.
    intros.
    specialize (X m).
    unfold valTC_Trans in X0.
    assert (EnvTyping (mkVEnv tenv (listTypTr (map snd tenv) X0)) tenv).
    + apply envTypingListTT.
    + apply X in X1.
      exact X1.
  - (* funs *)
    unfold E_Trans, F_Trans.
    intros.
    unfold FTyp_Trans.
    intros.
    assert (FEnvTyping fenv' ftenv').
    + rewrite h1.
      rewrite h2.
      eapply updateFEnvLemma.
      exact m.
      exact k2.
    + specialize (X X2).
      (* unfold FTyp_Trans in X0. *)      
      unfold valTC_Trans in X1. 
      assert (EnvTyping (mkVEnv tenv (listTypTr (map snd tenv) X1)) tenv).
      * apply envTypingListTT.
      * apply X in X3.
        exact X3.
  - (* QF *)
    unfold Q_Trans, F_Trans.
    intros.
    exact X.
  - (* FVar *)
    unfold Par_SSB, Q_Trans, F_Trans.
    intros.
    destruct ft.
    inversion X; subst; clear X.
    exact X3.
  - (* modify *)
    unfold E_Trans.
    intros.
    simpl.
    destruct XF.
    unfold MM.
    inversion k; subst.
    + inversion H; subst.
      subst T.
      simpl in H0.
      destruct v.
      destruct v.
      simpl in H0.
      clear k.
      clear H.
      clear H1.
      rewrite H0 in v.
      intros.
      exact (b_eval0 X1 v, b_exec0 X1 v). 
    + inversion X1; subst.
      eapply ExRelValT with (x0:=x) (t:=vtyp T1) in X0.
      destruct X0.
      destruct x0.
      destruct v0.
      inversion v; subst.
      subst T.
      simpl in H.
      clear f.
      clear v.
      clear H0.
      rewrite H in v0. 
      intros.
      exact (b_eval0 X0 v0, b_exec0 X0 v0). 
      exact X2. 
  - (* return *)
    unfold E_Trans.
    intros.
    simpl.
    inversion k; subst.  
    + inversion H; subst.
      subst T. 
      destruct v.    
      destruct v.
      simpl in H0.
      unfold VTyp_Trans.
      unfold vtypExt.
      clear k H H1.
      rewrite H0 in v.    
      exact (ret v).
    + inversion X1; subst.
      eapply ExRelValT with (x0:=x) (t0:=t) in X0.
      destruct X0.
      destruct x0.
      destruct v0.      
      inversion v; subst.
      subst T.
      simpl in H.
      clear f v H0.
      rewrite H in v0.   
      exact (ret v0).
      exact X2.
  - (* bindn *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X1 env X2).
    specialize (X0 X1 env X2).
    exact (bind X (fun _ => X0)).
  - (* binds *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X1 env X2).
    specialize (X0 X1).
    unfold MM.
    intros.
(**)
    unfold MM in X.
    apply X in X3.
    destruct X3.
    eapply (updateVEnvLemma env tenv x
                            (cst (VTyp_Trans t1) v) t1) in X2.
    specialize (X0 (updateE env x (cst (VTyp_Trans t1) v))).
    rewrite h in X0.
    apply X0 in X2.
    apply (X2 w).
    unfold VTyp_Trans.
    unfold vtypExt.
    constructor.
    simpl.
    reflexivity.
    constructor.
  - (* bindms *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (overrideFEnvLemma 
                                  fenvP fenv ftenvP ftenv m2 X0).  
    intro.
    rewrite h2 in X.
    rewrite h3 in X.
    specialize (X X2).
    specialize (overrideVEnvLemma envP env tenvP tenv k1 X1).
    intros.
    rewrite h1 in X.
    apply X in X3.
    exact X3.
  - (* apply *)
    unfold E_Trans, Q_Trans, P_Trans.
    intros.
    specialize (X X1).
    specialize (X0 X1 env X2).     
    simpl in X.
    inversion k2; subst.
    unfold env2ptyp in H3.
    inversion H3; subst. 
    simpl in X0.
    unfold MM; intros.
    unfold MM in X0.
    specialize (X0 X4); clear X4.
    destruct X0.
    clear H3.
    specialize (X t0).
    
    unfold MM in X.
    apply (X w).    

  - (* val *)
    unfold E_Trans.
    intros.
    simpl.
    unfold VTyp_Trans.
    unfold vtypExt.
    inversion k.
    subst T.
    rewrite <- H.
    exact (ret (cstExt v)).
  - (* ifthenelse *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X2 env X3).
    specialize (X0 X2 env X3).
    specialize (X1 X2 env X3).
    
    unfold MM; intro.
    unfold MM in X.
    specialize (X X4).
    destruct X.
    simpl in v.
    destruct v.
    exact (X0 w).
    exact (X1 w).
  - unfold Par_SSL, P_Trans.
    unfold E_Trans.
    intros.
    simpl.
    induction X.
    simpl.
    exact (ret tt).
    simpl.
    specialize (p0 X0 env X1).
    inversion m; subst.
    specialize (IHX X3).
    unfold MM; intro.
    specialize (p0 X4).
    destruct p0.
    specialize (IHX w).
    destruct IHX.
    exact (v, t, w0).
Defined.    

Next Obligation.

  revert X0.
  revert env.
  revert X.
  revert ET.
  revert ps ts.
  eapply ParTypingTrans_rect.

  - (* forall2_nil *)
    unfold Par_SSL.
    intros.
    constructor.
  - (* forall2_cons *)
    unfold Par_SSL.
    intros.
    econstructor.
    exact X0.
    exact X.  
  - (* matchenvs_nil *)
    unfold Par_SSA.
    constructor.
  - (* matchenvs_cons *)
    unfold Par_SSA.
    intros.
    econstructor.
    exact X0.
    exact X.    
  - (* matchenvs2_split *)
    unfold Par_SSB, Par_SSA.
    intros.
    econstructor.
    exact m0.
    exact m1.
    assumption.
    assumption.
    exact X.
    exact X0.
    exact X1.
  - (* funz *) 
    unfold E_Trans, F_Trans.  
    unfold FTyp_Trans.
    intros.
    specialize (X m).
    unfold valTC_Trans in X0.
    assert (EnvTyping (mkVEnv tenv0 (listTypTr (map snd tenv0) X0)) tenv0).
    + apply envTypingListTT.
    + apply X in X1.
      exact X1.
  - (* funs *)
    unfold E_Trans, F_Trans.
    intros.
    unfold FTyp_Trans.
    intros.
    assert (FEnvTyping fenv' ftenv').
    + rewrite h1.
      rewrite h2.
      eapply updateFEnvLemma.
      exact m.
      exact k2.
    + specialize (X X2).
      (* unfold FTyp_Trans in X0. *)      
      unfold valTC_Trans in X1. 
      assert (EnvTyping (mkVEnv tenv0 (listTypTr (map snd tenv0) X1)) tenv0).
      * apply envTypingListTT.
      * apply X in X3.
        exact X3.
  - (* QF *)
    unfold Q_Trans, F_Trans.
    intros.
    exact X.
  - (* FVar *)
    unfold Par_SSB, Q_Trans, F_Trans.
    intros.
    destruct ft.
    inversion X; subst; clear X.
    exact X3.
  - (* modify *)
    unfold E_Trans.
    intros.
    simpl.
    destruct XF.
    unfold MM.
    inversion k; subst.
    + inversion H; subst.
      subst T.
      simpl in H0.
      destruct v.
      destruct v.
      simpl in H0.
      clear k.
      clear H.
      clear H1.
      rewrite H0 in v.
      intros.
      exact (b_eval0 X1 v, b_exec0 X1 v). 
    + inversion X1; subst.
      eapply ExRelValT with (x0:=x) (t:=vtyp T1) in X0.
      destruct X0.
      destruct x0.
      destruct v0.
      inversion v; subst.
      subst T.
      simpl in H.
      clear f.
      clear v.
      clear H0.
      rewrite H in v0. 
      intros.
      exact (b_eval0 X0 v0, b_exec0 X0 v0). 
      exact X2. 
  - (* return *)
    unfold E_Trans.
    intros.
    simpl.
    inversion k; subst.  
    + inversion H; subst.
      subst T. 
      destruct v.    
      destruct v.
      simpl in H0.
      unfold VTyp_Trans.
      unfold vtypExt.
      clear k H H1.
      rewrite H0 in v.    
      exact (ret v).
    + inversion X1; subst.
      eapply ExRelValT with (x0:=x) (t0:=t) in X0.
      destruct X0.
      destruct x0.
      destruct v0.      
      inversion v; subst.
      subst T.
      simpl in H.
      clear f v H0.
      rewrite H in v0.   
      exact (ret v0).
      exact X2.
  - (* bindn *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X1 env X2).
    specialize (X0 X1 env X2).
    exact (bind X (fun _ => X0)).
  - (* binds *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X1 env X2).
    specialize (X0 X1).
    unfold MM.
    intros.
(**)
    unfold MM in X.
    apply X in X3.
    destruct X3.
    eapply (updateVEnvLemma env tenv0 x
                            (cst (VTyp_Trans t1) v) t1) in X2.
    specialize (X0 (updateE env x (cst (VTyp_Trans t1) v))).
    rewrite h in X0.
    apply X0 in X2.
    apply (X2 w).
    unfold VTyp_Trans.
    unfold vtypExt.
    constructor.
    simpl.
    reflexivity.
    constructor.
  - (* bindms *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (overrideFEnvLemma
                                  fenvP fenv0 ftenvP ftenv0 m2 X0).  
    intro.
    rewrite h2 in X.
    rewrite h3 in X.
    specialize (X X2).
    specialize (overrideVEnvLemma envP env tenvP tenv0 k1 X1).
    intros.
    rewrite h1 in X.
    apply X in X3.
    exact X3.
  - (* apply *)
    unfold E_Trans, Q_Trans, P_Trans.
    intros.
    specialize (X X1).
    specialize (X0 X1 env X2).     
    simpl in X.
    inversion k2; subst.
    unfold env2ptyp in H3.
    inversion H3; subst. 
    simpl in X0.
    unfold MM; intros.
    unfold MM in X0.
    specialize (X0 X4); clear X4.
    destruct X0.
    clear H3.
    specialize (X t0).
    
    unfold MM in X.
    apply (X w).    

  - (* val *)
    unfold E_Trans.
    intros.
    simpl.
    unfold VTyp_Trans.
    unfold vtypExt.
    inversion k.
    subst T.
    rewrite <- H.
    exact (ret (cstExt v)).
  - (* ifthenelse *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X2 env X3).
    specialize (X0 X2 env X3).
    specialize (X1 X2 env X3).
    
    unfold MM; intro.
    unfold MM in X.
    specialize (X X4).
    destruct X.
    simpl in v.
    destruct v.
    exact (X0 w).
    exact (X1 w).
  - unfold Par_SSL, P_Trans.
    unfold E_Trans.
    intros.
    simpl.
    induction X.
    simpl.
    exact (ret tt).
    simpl.
    specialize (p0 X0 env X1).
    inversion m; subst.
    specialize (IHX X3).
    unfold MM; intro.
    specialize (p0 X4).
    destruct p0.
    specialize (IHX w).
    destruct IHX.
    exact (v, t, w0).
Defined.    

Next Obligation.

  revert X.
  revert ET.
  revert q ft.
  eapply QFunTypingTrans_rect.

  - (* forall2_nil *)
    unfold Par_SSL.
    intros.
    constructor.
  - (* forall2_cons *)
    unfold Par_SSL.
    intros.
    econstructor.
    exact X0.
    exact X.  
  - (* matchenvs_nil *)
    unfold Par_SSA.
    constructor.
  - (* matchenvs_cons *)
    unfold Par_SSA.
    intros.
    econstructor.
    exact X0.
    exact X.    
  - (* matchenvs2_split *)
    unfold Par_SSB, Par_SSA.
    intros.
    econstructor.
    exact m0.
    exact m1.
    assumption.
    assumption.
    exact X.
    exact X0.
    exact X1.
  - (* funz *) 
    unfold E_Trans, F_Trans.  
    unfold FTyp_Trans.
    intros.
    specialize (X m).
    unfold valTC_Trans in X0.
    assert (EnvTyping (mkVEnv tenv (listTypTr (map snd tenv) X0)) tenv).
    + apply envTypingListTT.
    + apply X in X1.
      exact X1.
  - (* funs *)
    unfold E_Trans, F_Trans.
    intros.
    unfold FTyp_Trans.
    intros.
    assert (FEnvTyping fenv' ftenv').
    + rewrite h1.
      rewrite h2.
      eapply updateFEnvLemma.
      exact m.
      exact k2.
    + specialize (X X2).
      (* unfold FTyp_Trans in X0. *)      
      unfold valTC_Trans in X1. 
      assert (EnvTyping (mkVEnv tenv (listTypTr (map snd tenv) X1)) tenv).
      * apply envTypingListTT.
      * apply X in X3.
        exact X3.
  - (* QF *)
    unfold Q_Trans, F_Trans.
    intros.
    exact X.
  - (* FVar *)
    unfold Par_SSB, Q_Trans, F_Trans.
    intros.
    destruct ft.
    inversion X; subst; clear X.
    exact X3.
  - (* modify *)
    unfold E_Trans.
    intros.
    simpl.
    destruct XF.
    unfold MM.
    inversion k; subst.
    + inversion H; subst.
      subst T.
      simpl in H0.
      destruct v.
      destruct v.
      simpl in H0.
      clear k.
      clear H.
      clear H1.
      rewrite H0 in v.
      intros.
      exact (b_eval0 X1 v, b_exec0 X1 v). 
    + inversion X1; subst.
      eapply ExRelValT with (x0:=x) (t:=vtyp T1) in X0.
      destruct X0.
      destruct x0.
      destruct v0.
      inversion v; subst.
      subst T.
      simpl in H.
      clear f.
      clear v.
      clear H0.
      rewrite H in v0. 
      intros.
      exact (b_eval0 X0 v0, b_exec0 X0 v0). 
      exact X2. 
  - (* return *)
    unfold E_Trans.
    intros.
    simpl.
    inversion k; subst.  
    + inversion H; subst.
      subst T. 
      destruct v.    
      destruct v.
      simpl in H0.
      unfold VTyp_Trans.
      unfold vtypExt.
      clear k H H1.
      rewrite H0 in v.    
      exact (ret v).
    + inversion X1; subst.
      eapply ExRelValT with (x0:=x) (t0:=t) in X0.
      destruct X0.
      destruct x0.
      destruct v0.      
      inversion v; subst.
      subst T.
      simpl in H.
      clear f v H0.
      rewrite H in v0.   
      exact (ret v0).
      exact X2.
  - (* bindn *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X1 env X2).
    specialize (X0 X1 env X2).
    exact (bind X (fun _ => X0)).
  - (* binds *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X1 env X2).
    specialize (X0 X1).
    unfold MM.
    intros.
(**)
    unfold MM in X.
    apply X in X3.
    destruct X3.
    eapply (updateVEnvLemma env tenv x
                            (cst (VTyp_Trans t1) v) t1) in X2.
    specialize (X0 (updateE env x (cst (VTyp_Trans t1) v))).
    rewrite h in X0.
    apply X0 in X2.
    apply (X2 w).
    unfold VTyp_Trans.
    unfold vtypExt.
    constructor.
    simpl.
    reflexivity.
    constructor.
  - (* bindms *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (overrideFEnvLemma 
                                  fenvP fenv0 ftenvP ftenv0 m2 X0).  
    intro.
    rewrite h2 in X.
    rewrite h3 in X.
    specialize (X X2).
    specialize (overrideVEnvLemma envP env tenvP tenv k1 X1).
    intros.
    rewrite h1 in X.
    apply X in X3.
    exact X3.
  - (* apply *)
    unfold E_Trans, Q_Trans, P_Trans.
    intros.
    specialize (X X1).
    specialize (X0 X1 env X2).     
    simpl in X.
    inversion k2; subst.
    unfold env2ptyp in H3.
    inversion H3; subst. 
    simpl in X0.
    unfold MM; intros.
    unfold MM in X0.
    specialize (X0 X4); clear X4.
    destruct X0.
    clear H3.
    specialize (X t0).
    
    unfold MM in X.
    apply (X w).    

  - (* val *)
    unfold E_Trans.
    intros.
    simpl.
    unfold VTyp_Trans.
    unfold vtypExt.
    inversion k.
    subst T.
    rewrite <- H.
    exact (ret (cstExt v)).
  - (* ifthenelse *)
    unfold E_Trans.
    intros.
    simpl.
    specialize (X X2 env X3).
    specialize (X0 X2 env X3).
    specialize (X1 X2 env X3).
    
    unfold MM; intro.
    unfold MM in X.
    specialize (X X4).
    destruct X.
    simpl in v.
    destruct v.
    exact (X0 w).
    exact (X1 w).
  - unfold Par_SSL, P_Trans.
    unfold E_Trans.
    intros.
    simpl.
    induction X.
    simpl.
    exact (ret tt).
    simpl.
    specialize (p0 X0 env X1).
    inversion m; subst.
    specialize (IHX X3).
    unfold MM; intro.
    specialize (p0 X4).
    destruct p0.
    specialize (IHX w).
    destruct IHX.
    exact (v, t, w0).
Defined.    

End Reflect.