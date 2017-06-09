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

(**)
Definition Type_foldl (B: Type)
           (f: Type -> B -> Type) (ls: list B) : Type :=
  fold_left f ls unit. 

Fixpoint TList_Trans (ts: list VTyp) : Type :=
  match ts with
      | nil => unit
      | (t::ts') => (VTyp_Trans t) * (TList_Trans ts')
  end.                                    
(*
Definition TList_Trans (vts: list VTyp) : Type :=
     Type_foldl VTyp (fun t vt => prod (VTyp_Trans vt) t) vts.
*)

Fixpoint tlist2type (ts: list Type) : Type :=
  match ts with
    | nil => unit
    | (t::ts') => t * tlist2type ts'
  end.                               
(*
Definition tlist2type (ts: list Type) : Type :=
     Type_foldl Type (fun t1 t2 => prod t1 t2) ts.
*)
(**)


Definition valTC_Trans (tenv: valTC) : Type := TList_Trans (map snd tenv).

Definition PTyp_Trans (pt: PTyp) : Type :=
  match pt with
      PT ts => TList_Trans ts
  end.                 

(**)

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
Print listTypTr.
Print list_rect.
(*
Show Proof.
(fun (xts : list VTyp) (ps : TList_Trans xts) =>

 list_rect (fun xts0 : list VTyp => TList_Trans xts0 -> list Value)
           (fun _ : TList_Trans [] => [])
           (fun (a : VTyp) (xts0 : list VTyp)
                (IHxts : TList_Trans xts0 -> list Value)
                (ps0 : TList_Trans (a :: xts0)) =>
              let X :=
                let (X, X0) := ps0 in
                (fun (X1 : VTyp_Trans a) (X2 : TList_Trans xts0) =>
                let X3 := IHxts X2 in cst (VTyp_Trans a) X1 :: X3) X X0 in
              X) 

     xts ps)

Print list_rect.
list_rect = 
fun (A : Type) 
    (P : list A -> Type) 
    (f : P [])
    (f0 : forall (a : A) (l : list A), P l -> P (a :: l)) =>
fix F (l : list A) : P l :=
  match l as l0 return (P l0) with
  | [] => f
  | y :: l0 => f0 y l0 (F l0)
  end
     : forall (A : Type) (P : list A -> Type),
       P [] ->
       (forall (a : A) (l : list A), P l -> P (a :: l)) ->
       forall l : list A, P l

 *)
(*
Print listTypTr.
listTypTr = 

fix listTypTr (xts : list VTyp) (ps : TList_Trans xts) {struct xts} :
  list Value := 

listTypTr_obligation_1 xts ps
     : forall xts : list VTyp, TList_Trans xts -> list Value
*)

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

(**)

Definition FTyp_Trans (ft: FTyp) : Type :=
  valTC_Trans (extParType ft) -> MM W (VTyp_Trans (extRetType ft)).

(*
Definition funTC_Trans (tenv: funTC) : Type :=
     Type_foldl VTyp (fun t entry => prod (FTyp_Trans (snd entry)) t) tenv.
*)

Fixpoint funTC_Trans (tenv: funTC) : Type :=
  match tenv with
      | nil => unit
      | (t::ts) => (FTyp_Trans (snd t)) * (funTC_Trans ts)
  end.                                    

Definition Value_Trans (v: Value) :  projT1 v := cstExt v.

(*********************)

Inductive IsTypeList : list Type -> list Value -> Type :=
  | IsTLN : IsTypeList nil nil
  | IsTLC : forall (ts: list Type) (vs: list Value) (t: Type) (v: t),
              IsTypeList ts vs -> IsTypeList (t::ts) (cst t v::vs).

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
  Show Proof.
Defined.  


Program Fixpoint listTypTrA (xts: list Type) (ps : tlist2type xts) :
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
  exact (cst a X :: X0).
Defined.


(**********************************)

Lemma valTypId (xts: list Type) (ps : tlist2type xts) :
  xts = map valTyp (listTypTrA xts ps).
  revert ps.
  induction xts.
  auto.
  intros.  
  destruct ps.
  simpl.
  specialize (IHxts t).
  rewrite IHxts at 1.
(*
  unfold listTypTrA_obligation_1.
  unfold list_rect.
  simpl.
  unfold listTypTrA. 
*) 
  destruct xts.
  auto. 
  auto.
Defined.  

Lemma valTypId2 (xts: list Type) (ps : tlist2type xts) :
  tlist2type xts = vList_Typ_Trans (listTypTrA xts ps).
  unfold vList_Typ_Trans.
  rewrite valTypId at 1.
  reflexivity.
Defined.
(*
  revert ps.
  dependent induction xts.
  auto.
  intros.  
  destruct ps.
  unfold tlist2type.
 
  specialize (IHxts t).
  simpl.
  unfold tlist2type in IHxts.
  rewrite IHxts.

  destruct xts.
  auto. 
  auto.
Defined.  
*)
Lemma tlist2vListTypTrans (xts: list Type) :
  tlist2type xts -> forall  (ps : tlist2type xts),
                       vList_Typ_Trans (listTypTrA xts ps).
  intros.
  rewrite (valTypId2 xts ps) in X.
  auto.
Defined.


Lemma TListId (xts: list VTyp) (ps : TList_Trans xts) :
  TList_Trans xts = vList_Typ_Trans (listTypTr xts ps).
  revert ps.
  dependent induction xts.
  intros.
  simpl.
  reflexivity.
  intros.
  destruct ps.
  simpl.
  unfold vList_Typ_Trans.
  unfold tlist2type.
  simpl.

  specialize (IHxts t).
  rewrite IHxts.

  destruct xts.
  auto.
  auto.
Defined.

Lemma TListTrans2vListTypTrans (xts: list VTyp) :
  TList_Trans xts -> forall  (ps : TList_Trans xts),
                       vList_Typ_Trans (listTypTr xts ps).
  intros.
  rewrite (TListId xts ps) in X.
  auto.
Defined.


(********************************************)

(*
Lemma listTypTrIdA (xts: list Type) (ps : tlist2type xts) :
  (vList_Trans (listTypTrA xts ps)) = ps.
Toplevel input, characters 119-121:

Error:
In environment
xts : list Type
ps : tlist2type xts
The term "ps" has type "tlist2type xts" while it is expected to have type
 "vList_Typ_Trans (listTypTrA xts ps)".
*)

Lemma listTypTrIdA (xts: list Type) (ps : tlist2type xts) :
  JMeq (vList_Trans (listTypTrA xts ps)) ps.
revert ps.
dependent induction xts.
intros.
simpl.
destruct ps.
auto.
intros.
destruct ps.
specialize (IHxts t).

simpl.
unfold Value_Trans.
unfold cstExt.
simpl.

assert (vList_Trans_obligation_1 (listTypTrA_obligation_1 xts t) ~= t).
rewrite <- IHxts.
destruct xts.
auto.
simpl.

assert (forall x, vList_Trans_obligation_1 x = vList_Trans x).
intros.
destruct x.
auto.
simpl.
auto.
rewrite H.
auto.

Admitted.

(*
eapply JMeq_congr with (f:= fun x => (a0,x)) in H. 

eapply f_eq_dep with (f:= fun t k => ...)

eapply eq_dep_id_JMeq.

eapply JMeq_congr with (f:= fun x => (a0,x)).

assert (forall t,
          (t = tlist2vListTypTrans xts (vList_Trans_obligation_1 (listTypTrA_obligation_1 xts t))) -> 
 (fun x =>  (a0, vList_Trans_obligation_1 (listTypTrA_obligation_1 xts t)) ~=     (a0, x)) t).

generalize H.
generalize IHxts.
generalize t.

assert (fun t => vList_Trans_obligation_1 (listTypTrA_obligation_1 xts t) = fun t : tlist2type xts => t).

rewrite <- H.

clear IHxts.

eapply JMeq_eq in H.

destruct xts.
rewrite H.
auto.
simpl.
simpl in H.
inversion H; subst.
destruct t.
rewrite <- H at 1.

inversion t; subst.
rewrite H at 1.

rewrite H.

assert (exists w: vList_Typ_Trans (listTypTr xts t), t ~= w).
eexists.
clear H.
instantiate (1:= ff xts (listTypTr xts t) t).
*)


(*
Lemma TListId1 (xts: list VTyp) :
  sigT (fun _: TList_Trans xts  => TList_Trans xts) =
  sigT (fun ps => vList_Typ_Trans (listTypTr xts ps)).
  dependent induction xts.
  intros.
  simpl.
  reflexivity.
  intros.
  simpl.
  unfold vList_Typ_Trans.
  unfold tlist2type.
  simpl.

  specialize (IHxts t).
  rewrite IHxts.

  destruct xts.
  auto.
  auto.
Defined.
*)

(*
  assert   
  ((TList_Trans xts)%type =
  (fix tlist2type (ts : list Type) : Type :=
      match ts with
      | [] => unit
      | t0 :: ts' => prod t0 (tlist2type ts')
      end) (map valTyp (listTypTr_obligation_1 xts t))%type).
 
  specialize (IHxts t).
  rewrite IHxts.
  unfold vList_Typ_Trans.
  unfold tlist2type.
  
  
  assert (listTypTr xts t = listTypTr_obligation_1 xts t).
  destruct xts.
  auto.
  simpl.
  auto.
*)  
  (* TList_Trans: list VTyp -> Type *)
(* listTypTr: forall xts: list VTyp, TList_Trans xts -> list Value *)
(* vList_Trans: forall ls: list Value, tlist2type (map valTyp ls) *) 

(*
Lemma listTypTrIdA (xts: list VTyp) (ps : TList_Trans xts) :
  exists x: TList_Trans xts,
    JMeq (vList_Trans (listTypTr xts ps)) x.
  eexists.
  instantiate (1:= vList_Trans (listTypTr xts ps)).
    
*)  


Lemma listTypTrId (xts: list VTyp) (ps : TList_Trans xts) :
  JMeq (vList_Trans (listTypTr xts ps)) ps.
revert ps.
dependent induction xts.
intros.
simpl.
destruct ps.
auto.
intros.
destruct ps.
specialize (IHxts t).

simpl.
unfold Value_Trans.
unfold cstExt.
simpl.

assert (vList_Trans_obligation_1 (listTypTr_obligation_1 xts t) ~= t).
rewrite <- IHxts.
destruct xts.
auto.
simpl.

assert (forall x, vList_Trans_obligation_1 x = vList_Trans x).
intros.
destruct x.
auto.
simpl.
auto.
rewrite H.
auto.
clear IHxts.

assert (exists w: vList_Typ_Trans (listTypTr xts t), t ~= w).
eexists.
clear H.

Admitted.

(*
instantiate (1:= TListTrans2vListTypTrans xts (listTypTr xts t) t).

eapply JMeq_rect with (P:= fun t => (v, vList_Trans_obligation_1 (listTypTr_obligation_1 xts t)) ~= (v, t)).
instantiate (1:= vList_Trans_obligation_1 (listTypTr_obligation_1 xts t)).

revert H.
revert t.
rewrite TListId at 1.

rewrite <- H.

unfold vList_Trans.
unfold vList_Trans_obligation_1 at 1.

unfold vList_Trans.


unfold ValueI2T.
simpl.

rewrite <- IHxts at 2.
*)

(*********************************************************)

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