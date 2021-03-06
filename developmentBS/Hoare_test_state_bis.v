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
Require Import Hardware_Deep_v2_bis.
Require Import Coq.Logic.EqdepFacts.
Require Import IdModA_M2_bis.
Require Import Peano_dec.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Program.Equality.
Require Import Coq.Structures.Equalities.

Module Hoare_Test_state_bis <: IdModType.

Module HardwareC := Hardware_bis IdModA_M2_b.
Export HardwareC.

Definition Id := HardwareC.Id.
Definition IdEqDec := HardwareC.IdEqDec.
Definition IdEq := HardwareC.IdEq.
Definition W := HardwareC.W.
Definition Loc_PI := HardwareC.Loc_PI.
Definition BInit := HardwareC.BInit.
Definition WP := HardwareC.WP.


(**************************************************)

Open Scope string_scope.

(*** pepin src definitions*)

Definition multiplexer:page := P 1.

Definition PRidx:index := I 0.   (* descriptor *)
Definition PDidx:index := I 2.   (* page directory *)
Definition sh1idx:index := I 4. (* shadow 1*)
Definition sh2idx:index := I 6. (* shadow 2*)
Definition sh3idx:index := I 8. (* configuration pages list*)
Definition PPRidx:index := I 10. (* parent (virtual address is null) *)



Fixpoint findD (m: list (paddr * sValue)) (pad: paddr) (v: sValue)  : sValue :=
  match m with
     | nil => v
     | cons ((P p,I i) , v') ls =>
                     match pad with | (P p0,I i0) =>
                              match (eq_nat_dec p p0,eq_nat_dec i i0) with
                              | (left _ , left _) => v'
                              |  _ => findD ls pad v
                              end       
                     end       
    end.

Definition isVA table idx s: Prop := match findD (s.(memory)) (table,idx) (SP (P 0)) with 
             |SVA _ => True
             |_ => False
             end.

Definition nextEntryIsPP table idx (tableroot:Value) s : Prop:= 
match findD (s.(memory)) (table,(I (Vindex idx +1))) (SP (P 0)) with 
                  | SP table => tableroot = cst sValue (SP table)
                  |_ => False 
end.


Definition xf_read (p: page) : XFun index sValue := {|
   b_mod := fun s i => (s, findD (s.(memory)) (p,i) (SP (P 0)))    
|}.                                                    


Definition xf_succ : XFun index index := {|
   b_mod := fun s i =>  (s, (I (Vindex i+1)))    
|}.     

Instance VT_svalue : ValTyp sValue.
Instance VT_index : ValTyp index.


Definition Read (p:page) (x:Id) : Exp :=
  Modify index sValue VT_index VT_svalue (xf_read p) (Var x). 


Definition Succ (x:Id) : Exp :=
  Modify index index VT_index VT_index xf_succ (Var x). 


Definition getSh1idx : Exp := Val (cst index sh1idx).  (* shadow1 *) 
(**** with return to look like the original *)

(*
Definition getFstShadow (partition : page):=
  perform idx11 := getSh1idx in
  perform idx := MALInternal.Index.succ idx11 in
  readPhysical partition idx.
*)

Definition getFstShadow (p:page) : Exp :=
 BindS "x" getSh1idx 
           (BindS "y" (Succ "x") 
                      (Read p "y")
           ).


Definition partitionDescriptorEntry s := 
forall (p : page),  
In p (s.(partitions)) -> 
forall (idx : index), (idx = PDidx \/ idx = sh1idx \/ idx = sh2idx \/ idx = sh3idx \/ idx = PPRidx  \/ idx = PRidx ) ->
isVA p idx  s /\ 
exists p1 , nextEntryIsPP p idx (cst sValue (SP p1)) s  /\  
(cst page p1) <> (cst page page0).

(** Bind rules *)

Lemma bindn_congruence1 (P: W -> Prop)
      (fenv: funEnv) (env: valEnv) (e: Exp) :
    HoareTriple_Step P (fun _ => P) fenv env e ->
    forall e1: Exp,
       HoareTriple_Step P (fun _ => P) fenv env (BindN e e1).
Proof.
intros H1 e1.
unfold HoareTriple_Step.
intros s s' e' H2 H3.
unfold HoareTriple_Step in H1.
inversion H2;subst.
assumption.
eapply H1.
eauto.
assumption.
Qed.

Lemma bindn_congruence2 (P P1: W -> Prop)
      (fenv: funEnv) (env: valEnv) (e e': Exp) :
    HoareTriple_Step P (fun _ => P1) fenv env e ->
    (forall (e1: Exp) (v: Value),
       HoareTriple_Step P (fun _ => P1) fenv env (BindN (Val v) e1)) ->
    forall e1: Exp,
       HoareTriple_Step P (fun _ => P1) fenv env (BindN e e1).
Proof.
intros.
unfold HoareTriple_Step.
intros.
unfold HoareTriple_Step in H.
unfold HoareTriple_Step in H0.
inversion X;subst.
eapply H0.
eauto.
assumption.
eapply H.
eauto.
assumption.
Qed.


Lemma BindN_BStep1 (fenv: funEnv) (env: valEnv)
      (e1 e2: Exp) (v: Value) (s s': W) :
  (forall (e:Exp) (s: W), sigT (fun v: Value =>
                 sigT (fun s': W =>
      EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v))))) ->
  (forall (e:Exp) (s s1 s2: W) (v1 v2: Value),
      EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
      EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) ->
        (s1 = s2) /\ (v1 = v2)) ->
  EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s' (Val v)) ->
  (sigT2 (fun s1 : W =>
            (sigT (fun v1: Value =>
                     EClosure fenv env (Conf Exp s e1) (Conf Exp s1 (Val v1)))))
         (fun s1 : W =>
            EClosure fenv env (Conf Exp s1 e2) (Conf Exp s' (Val v)))).
Proof.
intros k1 k2 H.
specialize k1 with e1 s as k.
destruct k.
destruct s0.
specialize k1 with e2 x0 as k.
destruct k.
destruct s0.
econstructor.
econstructor.
eauto.
eapply BindN_extended_congruence in e as H1.
instantiate (1:=e2) in H1.
eapply EClosConcat in e0 as H2.
instantiate (1:=(Conf Exp x0 (BindN (Val x) e2))) in H2.
eapply EClosConcat in H2.
instantiate (1:=(Conf Exp s (BindN e1 e2))) in H2.
specialize k2 with (BindN e1 e2) s s' x2 v x1.
apply k2 in H.
destruct H.
rewrite H.
rewrite H0.
auto.
auto.
auto.
econstructor.
econstructor.
econstructor.
Qed.

Lemma BindN_VHT1 (P0 P1: W -> Prop) (P2: Value -> W -> Prop)

(fenv: funEnv) (env: valEnv) (e1 e2: Exp)

      (k1: forall (e:Exp) (s: W), sigT (fun v: Value =>
                 sigT (fun s': W =>
             EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v)))))

      (k2: forall (e:Exp) (s s1 s2: W) (v1 v2: Value),
          EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
          EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) ->
                (s1 = s2) /\ (v1 = v2)) :

  HoareTriple_Eval P0 (fun _ => P1) fenv env e1 ->
  HoareTriple_Eval P1 P2 fenv env e2 ->
  HoareTriple_Eval P0 P2 fenv env (BindN e1 e2).
Proof.
intros H1 H2.
unfold HoareTriple_Eval in *.
intros s s' v H3 H4.
eapply BindN_BStep1 in H3.
destruct H3.
destruct s0.
eapply H2.
eauto.
eapply H1.
eauto.
auto.
auto.
auto.
Qed.

Lemma simpl_BindMS : 
forall (fenv fenv': funEnv) (env env': valEnv) (v : Value) (s : W),
  EClosure fenv env (Conf Exp s (BindMS fenv' env' (Val v))) (Conf Exp s (Val v)).
Proof.
intros.
econstructor.
econstructor.
econstructor.
Qed.

Lemma BindS_BStep1 (fenv: funEnv) (env: valEnv)
      (e1 e2: Exp) (x: Id) (v: Value) (s s': W)
  (k1: forall (fenv: funEnv) (env: valEnv) (e:Exp) (s: W),
       sigT (fun v: Value =>
                 sigT (fun s': W =>
             EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v)))))
  (k2: forall (e:Exp) (s s1 s2: W) (v1 v2: Value),
          EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
          EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) ->
                (s1 = s2) /\ (v1 = v2))  :
  EClosure fenv env (Conf Exp s (BindS x e1 e2)) (Conf Exp s' (Val v)) ->
  (sigT (fun s1 : W =>
            (sigT2 (fun v1: Value =>
                     EClosure fenv env (Conf Exp s e1) (Conf Exp s1 (Val v1)))
                   (fun v1: Value =>
                     EClosure fenv ((x,v1)::env) (Conf Exp s1 e2) (Conf Exp s' (Val v)))))).
Proof.
intros H.
specialize k1 with fenv env e1 s as k.
destruct k.
destruct s0.
specialize k1 with fenv ((x,x0)::env) e2 x1 as k.
destruct k.
destruct s0.
econstructor.
econstructor.
eauto.
clear k1.
eapply BindS_extended_congruence in e as H2.
instantiate (1:=e2) in H2.
instantiate (1:=x) in H2.
specialize BindS_EStep with fenv env x1 x x0 e2 as X.
unfold singleE in X.
unfold emptyE in X.
apply StepIsEClos in X.
eapply BindMS_extended_congruence in e0 as H3.
instantiate (1:=[(x,x0)]) in H3.
instantiate (1:=[]) in H3.
instantiate (1:=env) in H3.
instantiate (1:=fenv) in H3.
eapply EClosConcat in H3 as H4.
instantiate (1:=(Conf Exp s (BindS x e1 e2))) in H4.
specialize simpl_BindMS with fenv emptyE env [(x, x0)] x2 x3 as X0.
eapply EClosConcat in X0 as X1.
instantiate (1:=(Conf Exp s (BindS x e1 e2))) in X1.
specialize k2 with (BindS x e1 e2) s s' x3 v x2.
apply k2 in H.
clear k2.
destruct H.
rewrite H.
rewrite H0.
auto.
auto.
auto.
eapply EClosConcat in X as X1.
instantiate (1:=(Conf Exp s (BindS x e1 e2))) in X1.
auto.
auto.
auto.
auto.
Qed.


Lemma BindS_VHT1 (P0: W -> Prop) (P1 P2: Value -> W -> Prop)

(fenv: funEnv) (env: valEnv) (e1 e2: Exp) (x: Id)

 (k1: forall (fenv: funEnv) (env: valEnv) (e:Exp) (s: W),
       sigT (fun v: Value =>
                 sigT (fun s': W =>
             EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v)))))
 (k2: forall (e:Exp) (s s1 s2: W) (v1 v2: Value),
          EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
          EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) ->
                (s1 = s2) /\ (v1 = v2)) :

  HoareTriple_Eval P0 P1 fenv env e1 ->
  (forall v, HoareTriple_Eval (P1 v) P2 fenv ((x,v)::env) e2) ->
  HoareTriple_Eval P0 P2 fenv env (BindS x e1 e2).
Proof.
intros.
unfold HoareTriple_Eval in *.
intros.
eapply BindS_BStep1 in X.
destruct X.
destruct s0.
eapply H0.
eauto.
eapply H.
eauto.
auto.
auto.
auto.
Qed.


Lemma getSh1idxW (P: Value -> W -> Prop) (fenv: funEnv) (env: valEnv) :
  {{wp P fenv env getSh1idx}} fenv >> env >> getSh1idx {{P}}.
Proof.
apply wpIsPrecondition.
Qed.

Lemma getSh1idxWp P fenv env :
{{fun s => P s }} fenv >> env >> getSh1idx 
{{fun (idxSh1 : Value) (s : state) => P s  /\ idxSh1 = cst index sh1idx }}.
Proof.
eapply weaken.
eapply getSh1idxW.
intros. 
unfold wp.
intros.
split.
unfold getSh1idx in X.
inversion X;subst.
auto.
inversion X0.
inversion X;subst.
auto.
inversion X0.
Qed.

Definition succfn (i:index) : index := match i with | I n => I (n+1) end.


Lemma succW  (partition : page) (x:Id) (v:Value) P (fenv: funEnv) (env: valEnv) :
  {{fun s => P s /\ v = cst index sh1idx}} 
      fenv >> (x,v) :: env >> (Succ x)
  {{fun (idxsuc : Value) (s : state) => P s  /\ idxsuc = cst index (succfn sh1idx)}}.
Proof.
unfold HoareTriple_Eval.
intros.
destruct H.
unfold succfn.
simpl.
destruct v.
destruct v.
unfold cst in *.
inversion H0;subst.
repeat apply inj_pair2 in H3.
rewrite H3 in X.
clear H0 H3 v.
inversion X;subst.
inversion X0;subst. 
repeat apply inj_pair2 in H6.
rewrite H6 in X0. 
rewrite H6 in X1.  
inversion X2;subst.
inversion X3;subst.
inversion H0;subst.
destruct IdEqDec in H2. 
inversion H2;subst.
clear e H2 X3 H0 XF1.
inversion X1;subst.
inversion X4;subst.
inversion X3;subst.
repeat apply inj_pair2 in H6.
repeat apply inj_pair2 in H8.
rewrite H6. rewrite H8.
unfold b_exec.
unfold b_eval.
unfold xf_succ.
unfold b_mod.
simpl.
auto.
inversion X3;subst.
repeat apply inj_pair2 in H6.
repeat apply inj_pair2 in H8.
rewrite H6 in X5. rewrite H8 in X5.
unfold b_exec in X5.
unfold b_eval in X5.
unfold xf_succ in X5.
unfold b_mod in X5.
simpl in *.
inversion X5.
inversion X7.
contradiction.
Qed.

Lemma readPhysicalW y table (v:Value) (P' : Value -> W -> Prop) (fenv: funEnv) (env: valEnv) :
{{fun s => v = cst index (succfn sh1idx) /\ exists p1 ,findD (s.(memory)) (table,succfn sh1idx) (SP (P 0)) =  SP p1 /\ P' (cst sValue (SP p1)) s }} 
fenv >> (y,v)::env >> Read table y {{P'}}.
Proof.
unfold HoareTriple_Eval.
intros.
inversion H;subst.
clear H.
inversion H1;subst.
clear H1.
inversion H;subst.
clear H.
inversion X;subst.
inversion X0;subst.
repeat apply inj_pair2 in H7.
rewrite H7 in X1.
rewrite H7 in X0.
inversion X2;subst.
inversion X3;subst.
inversion H;subst.
destruct IdEqDec in H3.
inversion H3;subst.
clear H3 e X3 H XF1. 
inversion X0;subst.
repeat apply inj_pair2 in H7.
repeat apply inj_pair2 in H11.
inversion X1;subst.
inversion X4;subst.
repeat apply inj_pair2 in H7.
repeat apply inj_pair2 in H8.
repeat apply inj_pair2 in H9.
rewrite H7 in X4.
rewrite H9 in X4.
unfold xf_read at 2 in X4.
unfold b_eval in X4.
unfold b_exec in X4.
unfold b_mod in X4.
simpl in *.
rewrite H0 in X4.
rewrite H7 in X5.
rewrite H9 in X5.
unfold xf_read in X5.
unfold b_eval in X5.
unfold b_exec in X5.
unfold b_mod in X5.
simpl in *.
rewrite H0 in X5.
inversion X5;subst.
auto.
inversion X6.
repeat apply inj_pair2 in H7.
inversion X6.
contradiction.
Qed.

Lemma getFstShadow1 (partition : page) (P : W -> Prop) (fenv: funEnv) (env: valEnv)
  (k1: forall (fenv: funEnv) (env: valEnv) (e:Exp) (s: W),
       sigT (fun v: Value =>
                 sigT (fun s': W =>
             EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v)))))
  (k2: forall (fenv: funEnv) (env: valEnv) (e:Exp) (s s1 s2: W) (v1 v2: Value),
          EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
          EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) ->
                (s1 = s2) /\ (v1 = v2))  :
{{fun s => P s  /\ partitionDescriptorEntry s /\ In partition (s.(partitions))}}
fenv >> env >> (getFstShadow partition) 
{{fun (sh1 : Value) (s : state) => P s /\ nextEntryIsPP partition sh1idx sh1 s}}.
Proof.
unfold getFstShadow.
eapply BindS_VHT1.
eauto . eauto.
eapply getSh1idxWp.
intros.
simpl.
eapply BindS_VHT1.
eauto. eauto.
eapply succW.
auto.
intros.
simpl.
eapply weaken.
eapply readPhysicalW.
clear k1 k2.
intros.
simpl.
intuition.
subst.
unfold partitionDescriptorEntry in *.
apply H0 with partition sh1idx in H3.
clear H0.
intuition.
destruct H1.
intuition.
exists x.
intuition.
unfold nextEntryIsPP in H2.
simpl in *.
destruct (findD (memory s) (partition, I 5) (SP (IdModA_M2_b.P 0))) in *;try contradiction.
unfold cst in H2.
apply inj_pairT2 in H2.
inversion H2;subst.
auto.
auto.
Qed.



End Hoare_Test_state_bis.