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
Require Import Hardware_Deep_v2.
Require Import Coq.Logic.EqdepFacts.

Module Hoare_Test <: IdModType.

Module HardwareC := Hardware IdModM2.
Export HardwareC.

Definition Id := HardwareC.Id.
Definition IdEqDec := HardwareC.IdEqDec.
Definition IdEq := HardwareC.IdEq.
Definition W := HardwareC.W.
Definition Loc_PI := HardwareC.Loc_PI.
Definition BInit := HardwareC.BInit.
Definition WP := HardwareC.WP.

(**************************************************)

Open Scope state_scope.

Definition xf_read : XFun unit W := {|
   b_mod := fun x _ => (x, x)     
|}.                                                     

Definition xf_write : XFun W unit := {|
   b_mod := fun _ x => (x, tt)     
|}.                                                                                                      

Definition Read (VW: ValTyp W) : Exp :=
  Modify unit W UnitV VW xf_read (QV (cst unit tt)).

Definition Write (VW: ValTyp W) (x: nat) : Exp :=
  Modify W unit VW UnitV xf_write (QV (cst nat x)).

Definition ReadN : Exp := Read NatV.

Definition WriteN (x: nat) : Exp := Write NatV x.

(** 1 *)

Lemma write_nat_1 (P0: nat -> Prop)
           (fenv: funEnv) (env: valEnv) (x: nat): 
  forall (s s': W) (e: Exp),
    EStep fenv env (Conf Exp s (WriteN x))
                      (Conf Exp s' e) ->
  P0 x -> P0 s'.
Proof.
intros s s' e H1 H2.
inversion H1; subst.
repeat apply inj_pair2 in H7.
apply inj_pair2 in H9.
rewrite H9.
rewrite H7.
unfold b_exec.
unfold b_mod.
unfold xf_write.
simpl.
auto.
inversion X.
Qed.


Definition WriteNat1SHT (P0: nat -> Prop)
                       (fenv: funEnv) (env: valEnv) (x: nat) :=
  HoareTriple_Step (fun _ => P0 x) (fun _ s => P0 s) fenv env (WriteN x).

Lemma write_nat_1_sht (P0: nat -> Prop)
           (fenv: funEnv) (env: valEnv) (x: nat): 
  forall (s s': W) (e: Exp),
    WriteNat1SHT P0 fenv env x.
Proof.
intros s s' e.
unfold WriteNat1SHT.
unfold HoareTriple_Step.
apply write_nat_1.
Qed.

(** 2 *)

Lemma write_nat_2 (P0: nat -> Prop)
           (fenv: funEnv) (env: valEnv) (x: nat): 
  forall (s s': W) (e: Exp),
    EStep fenv env (Conf Exp s (WriteN x))
                      (Conf Exp s' e) ->
  P0 x -> P0 s' /\ s' = x.
Proof.
intros s s' e H1 H2.
split.
eapply write_nat_1.
eauto. auto.
inversion H1;subst.
repeat apply inj_pair2 in H7.
apply inj_pair2 in H9.
rewrite H7.
rewrite H9.
unfold b_exec.
unfold xf_write.
unfold b_mod.
simpl.
reflexivity.
inversion X.
Qed.

Definition WriteNat2SHT (P0: nat -> Prop)
                       (fenv: funEnv) (env: valEnv) (x: nat) :=
  HoareTriple_Step (fun _ => P0 x) (fun _ s => P0 s /\ s = x)
                   fenv env (WriteN x).

Lemma write_nat_2_sht (P0: nat -> Prop)
           (fenv: funEnv) (env: valEnv) (x: nat): 
  forall (s s': W) (e: Exp),
    WriteNat2SHT P0 fenv env x.
intros s s' e.
unfold WriteNat2SHT.
unfold HoareTriple_Step.
apply write_nat_2.
Qed.

(** 3 *)

Lemma read_nat_1 (P0: Value -> Prop)
           (fenv: funEnv) (env: valEnv): 
  forall (s s': W) (v: Value),
    EClosure fenv env (Conf Exp s ReadN)
             (Conf Exp s' (Val v)) ->
    P0 (cst nat s) -> P0 v.
Proof.
intros s s' v H1 H2.
inversion H1;subst.
inversion X;subst.
repeat apply inj_pair2 in H7.
apply inj_pair2 in H9.
rewrite H7 in X.
rewrite H9 in X.
unfold xf_read in X.
unfold b_exec in X.
unfold b_eval in X.
unfold b_mod in X.
simpl in *.
rewrite H7 in X0.
rewrite H9 in X0.
unfold xf_read in X0.
unfold b_exec in X0.
unfold b_eval in X0.
unfold b_mod in X0.
simpl in *.
destruct v.
destruct v.
unfold cst in *.
inversion X0;subst.
apply inj_pair2 in H10.
eauto.
inversion X1;subst.
inversion X1.
Qed.



Definition ReadNat1SHT (P0: Value -> Prop)
                       (fenv: funEnv) (env: valEnv) :=
  HoareTriple_Step (fun s => P0 (cst nat s))
                   (fun e _ => forall v: Value,
                                 e = Val v -> P0 v) fenv env ReadN.

Definition ReadNat1VHT (P0: Value -> Prop)
                       (fenv: funEnv) (env: valEnv) :=
  HoareTriple_Eval (fun s => P0 (cst nat s))
                   (fun v _ => P0 v) fenv env ReadN.


(** 4 *)

Lemma read_nat_2 (P0: Value -> Prop)
           (fenv: funEnv) (env: valEnv): 
  forall (s s': W) (v: Value),
    EClosure fenv env (Conf Exp s ReadN)
             (Conf Exp s' (Val v)) ->
    P0 (cst nat s) -> P0 v /\ v = (cst nat s').
Proof.
intros s s' v H1 H2.
eauto.
split.
eapply read_nat_1.
eauto. auto.
destruct v.
destruct v.
unfold cst in *.
inversion H1;subst.
inversion X;subst.
repeat apply inj_pair2 in H7.
apply inj_pair2 in H9.
rewrite H7 in X.
rewrite H9 in X.
unfold xf_read in X.
unfold b_exec in X.
unfold b_eval in X.
unfold b_mod in X.
simpl in *.
rewrite H7 in X0.
rewrite H9 in X0.
unfold xf_read in X0.
unfold b_exec in X0.
unfold b_eval in X0.
unfold b_mod in X0.
simpl in *.
inversion X0;subst.
auto.
inversion X;subst.
inversion X1.
inversion X1.
Qed.


Definition ReadNat2SHT (P0: Value -> Prop)
                       (fenv: funEnv) (env: valEnv) :=
  HoareTriple_Step (fun s => P0 (cst nat s))
                   (fun e s => forall v: Value,
                          e = Val v -> P0 v /\ v = cst nat s) fenv env ReadN.

Definition ReadNat2VHT (P0: Value -> Prop)
                       (fenv: funEnv) (env: valEnv) :=
  HoareTriple_Eval (fun s => P0 (cst nat s))
                   (fun v s => P0 v /\ v = cst nat s) fenv env ReadN.



(** 5 *)

Lemma wread_nat_1 (P0: Value -> Prop)
           (fenv: funEnv) (env: valEnv) (x: nat): 
  forall (s s': W) (v: Value),
    EClosure fenv env (Conf Exp s (BindN (WriteN x) ReadN))
                      (Conf Exp s' (Val v)) ->
  P0 (cst nat x) -> P0 v.
Proof.
intros s s' v H1 H2.
inversion H1;subst.
inversion X;subst.
inversion X1;subst.
repeat apply inj_pair2 in H7.
apply inj_pair2 in H9.
rewrite H7 in X.
rewrite H9 in X.
unfold xf_write in X.
unfold b_exec in X.
unfold b_eval in X.
unfold b_mod in X.
simpl in *.
rewrite H7 in X0.
rewrite H9 in X0.
unfold xf_write in X0.
unfold b_exec in X0.
unfold b_eval in X0.
unfold b_mod in X0.
simpl in *.
rewrite H7 in X1.
rewrite H9 in X1.
unfold xf_write in X1.
unfold b_exec in X1.
unfold b_eval in X1.
unfold b_mod in X1.
simpl in *.
destruct v.
destruct v.
unfold cst in *.
inversion X0;subst.
inversion X2;subst.
inversion X3;subst.
inversion X4;subst.
repeat apply inj_pair2 in H7.
apply inj_pair2 in H10.
rewrite H7 in X5.
rewrite H10 in X5.
unfold b_exec in X5.
unfold b_eval in X5.
unfold xf_read in X5.
unfold b_mod in X5.
simpl in *.
rewrite H7 in X4.
rewrite H10 in X4.
unfold b_exec in X4.
unfold b_eval in X4.
unfold xf_read in X4.
unfold b_mod in X4.
simpl in *.
inversion X5;subst.
eauto.
inversion X6.
inversion X6.
inversion X4.
inversion X2.
Qed.


Definition WReadNat1EHT (P0: Value -> Prop)
           (fenv: funEnv) (env: valEnv) (x: nat) :=
  HoareTriple_ExtendedStep (fun _ => P0 (cst nat x))
                           (fun e _ => forall v: Value, e = Val v -> P0 v)
                           fenv env (BindN (WriteN x) ReadN).

Lemma wread_nat_1_eht (P0: Value -> Prop)
      (fenv: funEnv) (env: valEnv) (x: nat):
    WReadNat1EHT P0 fenv env x.
Proof.
unfold WReadNat1EHT.
unfold HoareTriple_ExtendedStep.
intros s s' e' H1 H2 v H3.
eapply wread_nat_1.
rewrite <- H3.
eauto. auto.
Qed.


Definition WReadNat1VHT (P0: Value -> Prop)
           (fenv: funEnv) (env: valEnv) (x: nat) :=
  HoareTriple_Eval (fun _ => P0 (cst nat x))
                    (fun v _ => P0 v)
                    fenv env (BindN (WriteN x) ReadN).
 
Lemma wread_nat_1_vht (P0: Value -> Prop)
      (fenv: funEnv) (env: valEnv) (x: nat):
    WReadNat1VHT P0 fenv env x.
Proof.
unfold WReadNat1VHT.
unfold HoareTriple_Eval.
eapply wread_nat_1.
Qed.

(** 6 *)

Lemma wread_nat_2 (P0: Value -> Prop)
           (fenv: funEnv) (env: valEnv) (x: nat): 
  forall (s s': W) (v: Value),
    EClosure fenv env (Conf Exp s (BindN (WriteN x) ReadN))
                      (Conf Exp s' (Val v)) ->
  P0 (cst nat x) -> P0 v /\ x = s' /\ v = cst nat x.
Proof.
intros s s' v H1 H2.
split.
eapply wread_nat_1.
eauto. auto.
split.
-inversion H1;subst.
 inversion X;subst.
 inversion X1;subst.
 repeat apply inj_pair2 in H7.
 apply inj_pair2 in H9.
 rewrite H7 in X.
 rewrite H9 in X.
 unfold b_exec in X.
 unfold b_eval in X.
 unfold xf_write in X.
 unfold b_mod in X.
 simpl in *.
 rewrite H7 in X0.
 rewrite H9 in X0.
 unfold b_exec in X0.
 unfold b_eval in X0.
 unfold xf_write in X0.
 unfold b_mod in X0.
 simpl in *.
 rewrite H7 in X1.
 rewrite H9 in X1.
 unfold b_exec in X1. 
 unfold b_eval in X1.
 unfold xf_write in X1.
 unfold b_mod in X1.
 simpl in *.
 inversion X0;subst.
 inversion X2;subst.
 inversion X3;subst.
 inversion X4;subst.
 repeat apply inj_pair2 in H7.
 apply inj_pair2 in H10.
 rewrite H7 in X5.
 rewrite H10 in X5.
 unfold b_exec in X5.
 unfold b_eval in X5.
 unfold xf_write in X5.
 unfold b_mod in X5.
 simpl in *.
 inversion X5;subst.
 auto.
 inversion X6.
 inversion X6.
 inversion X4.
 inversion X2.
-destruct v.
 destruct v.
 unfold cst in *.
 inversion H1;subst.
 inversion X;subst.
 inversion X1;subst.
 repeat apply inj_pair2 in H7.
 apply inj_pair2 in H9.
 rewrite H7 in X1.
 rewrite H9 in X1.
 unfold b_eval in X1.
 unfold b_exec in X1.
 unfold xf_write in X1.
 unfold b_mod in X1.
 simpl in *.
 rewrite H7 in X0.
 rewrite H9 in X0.
 unfold b_eval in X0.
 unfold b_exec in X0.
 unfold xf_write in X0.
 unfold b_mod in X0.
 simpl in *.
 rewrite H7 in X.
 rewrite H9 in X.
 unfold b_eval in X.
 unfold b_exec in X.
 unfold xf_write in X.
 unfold b_mod in X.
 simpl in *.
 inversion X1;subst.
 repeat apply inj_pair2 in H10.
 apply inj_pair2 in H12.
 apply inj_pair2 in H15.
 rewrite H10 in H1.
 unfold b_exec in H1.
 unfold xf_write in H1.
 unfold b_mod in H1.
 simpl in *.
 inversion H1;subst.
 inversion X2;subst.
 inversion X3;subst.
 inversion X4;subst.
 repeat apply inj_pair2 in H7.
 apply inj_pair2 in H10.
 rewrite H7 in X4.
 rewrite H10 in X4.
 unfold b_eval in X4.
 unfold b_exec in X4.
 unfold xf_write in X4.
 unfold b_mod in X4.
 simpl in *.
 rewrite H7 in X3.
 rewrite H10 in X3.
 unfold b_eval in X3.
 unfold b_exec in X3.
 unfold xf_write in X3.
 unfold b_mod in X3.
 simpl in *.
 rewrite H7 in X2.
 rewrite H10 in X2.
 unfold b_eval in X2.
 unfold b_exec in X2.
 unfold xf_write in X2.
 unfold b_mod in X2.
 simpl in *.
 inversion X5;subst.
 inversion X6;subst.
 inversion X7;subst.
 repeat apply inj_pair2 in H7.
 apply inj_pair2 in H13.
 rewrite H7 in X8.
 rewrite H13 in X8.
 unfold b_eval in X8.
 unfold b_exec in X8.
 unfold xf_write in X8.
 unfold xf_read in X8.
 unfold b_mod in X8.
 simpl in *.
 rewrite H7 in X7.
 rewrite H13 in X7.
 unfold b_eval in X7.
 unfold b_exec in X7.
 unfold xf_write in X7.
 unfold xf_read in X7.
 unfold b_mod in X7.
 simpl in *.
 inversion X8;subst.
 reflexivity.
 inversion X9;subst.
 inversion X9.
 inversion X7;subst.
 inversion X7.
 inversion X2.
Qed.


Definition WReadNat2VHT (P0: Value -> Prop)
           (fenv: funEnv) (env: valEnv) (x: nat) :=
  HoareTriple_Eval (fun _ => P0 (cst nat x))
                    (fun v s => P0 v /\ x = s /\ v = cst nat x)
                    fenv env (BindN (WriteN x) ReadN).
 
Lemma wread_nat_2_vht (P0: Value -> Prop)
      (fenv: funEnv) (env: valEnv) (x: nat):
    WReadNat2VHT P0 fenv env x.
Proof.
unfold WReadNat2VHT.
unfold HoareTriple_Eval.
eapply wread_nat_2.
Qed.

(** 7 *)

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




End Hoare_Test.

