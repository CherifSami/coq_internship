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

Module HDV1bis (*IdT: IdModType*) <: IdModType.

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

Definition hoareTriple_Step (P : W -> Prop)(fenv: funEnv) (env: valEnv)
           (e: Exp) (Q : Exp -> W -> Prop) :=
  forall (s s': W) (e': Exp),
    EStep fenv env (Conf Exp s e) (Conf Exp s' e') ->
    P s -> Q e' s'.

Notation "{{ P }} fenv >> env >> e {{ Q }}" := (hoareTriple_Step P fenv env e Q) 
(at level 90) : state_scope.

Open Scope state_scope.

Lemma conjProp (P R : W -> Prop) (Q : Exp -> W -> Prop) (fenv: funEnv) (env: valEnv) (e : Exp) :
{{ P }} fenv >> env >> e  {{ Q }} 
-> {{ R }} fenv >> env >> e {{fun _ => R}}
-> {{fun s => P s/\ R s}} fenv >> env >> e {{fun a s => Q a s/\ R s}}.
Proof.
intros H1 H2.
intros s s' e'.
intros H3 H4.
destruct H4 as [H4 H5].
split.
-unfold hoareTriple_Step in H1.
 apply H1 in H3.
 assumption. assumption.
-unfold hoareTriple_Step in H2.
 apply H2 in H3.
 assumption. assumption.
Qed.

Definition wp (P : Exp -> W -> Prop) (fenv: funEnv) (env: valEnv) (e : Exp) :
  W -> Prop := fun s => forall (e':Exp) (s': W), 
       EStep fenv env (Conf Exp s e) (Conf Exp s' e') -> P e' s'.

Lemma wpIsPrecondition (P : Exp -> W -> Prop) (fenv: funEnv) (env: valEnv) (e : Exp) :
  {{ wp P fenv env e }} fenv >> env >> e {{ P }}.
Proof.
unfold hoareTriple_Step.
intros s s' e' H1 H2.
unfold wp in H2.
auto.
Qed.

Lemma wpIsWeakestPrecondition(P : Exp -> W -> Prop) (Q : W -> Prop) (fenv: funEnv) (env: valEnv) (e : Exp) :
  {{ Q }} fenv >> env >> e {{ P }} -> forall s, Q s -> (wp P fenv env e) s.
Proof.
intros H1 s H2.
unfold wp.
intros e' s' H3.
apply H1 in H3.
auto.
Qed.


Lemma postAnd :
forall (P : W -> Prop) (Q R : Exp -> W -> Prop) (fenv: funEnv) (env: valEnv) (e : Exp),
  {{ P }} fenv >> env >> e {{ Q }} 
-> {{ P }} fenv >> env >> e {{ R }} 
-> {{ P }} fenv >> env >> e {{ fun a s => Q a s /\ R a s }}.
Proof.
intros P Q R fenv env e H1 H2.
intros a s.
intros e' H3 H4.
split.
-unfold hoareTriple_Step in H1.
 apply H1 in H3. 
 assumption. assumption.
-apply H2 in H3.
 auto.
Qed.


Lemma preOr :
  forall (P Q : W -> Prop) (R : Exp -> W -> Prop) (fenv: funEnv) (env: valEnv) (e : Exp),
  {{ P }} fenv >> env >> e {{ R }} 
-> {{ Q }} fenv >> env >> e {{ R }} 
-> {{ fun s => P s \/ Q s }} fenv >> env >> e {{ R }}.
Proof.
intros P Q R fenv env e H1 H2 s.
intros s' e' H3 H4.
destruct H4.
-apply H1 in H3 .
 auto.
-apply H2 in H3.
 auto.
Qed.

Lemma preAndPost : 
forall (P1 Q1 : W -> Prop) (P2  : Exp -> W -> Prop) (fenv: funEnv) (env: valEnv) (e : Exp),
{{P1}} fenv >> env >> e {{P2}} -> 
{{fun s => P1 s /\ Q1 s}} fenv >> env >> e {{fun a => Q1 }} -> 
{{fun s => P1 s /\ Q1 s}} fenv >> env >> e {{fun a s => P2 a s /\ Q1 s}}.
Proof.
intros P1 Q1 P2 fenv env e H1 H2 s s'.
intros e' H3 [H4 H5].
split.
-apply H1 in H3.
 auto.
-apply H2 in H3.
 apply H3.
 auto.
Qed.

Lemma andAssocHT  :
forall (P1 P2 P3 : W -> Prop) (R  : Exp -> W -> Prop) (fenv: funEnv) (env: valEnv) (e : Exp),
{{ fun s => (P1 s /\ P2 s) /\ P3 s }} fenv >> env >> e {{ R }} 
<-> {{ fun s => P1 s /\ P2 s /\ P3 s }} fenv >> env >> e {{ R }}.
Proof.
intros P1 P2 P3 R fenv env e.
split.
-intro H.
 unfold hoareTriple_Step.
 intros s s' e' H1 [H2 [H3 H4]].
 apply H in H1.
 apply H1.
 auto.
-intro s.
 unfold hoareTriple_Step.
 intros s0 s' e' H1 [[H2 H3] H4].
 apply s in H1.
 auto.
Qed.

Lemma permutHT :
forall (P1 P2 P3 : W -> Prop) (R  : Exp -> W -> Prop) (fenv: funEnv) (env: valEnv) (e : Exp),
{{ fun s => P1 s /\ P2 s /\ P3 s }} fenv >> env >> e {{ R }} 
<-> {{ fun s => P1 s /\ P3 s /\ P2 s }} fenv >> env >> e {{ R }}.
Proof.
intros P1 P2 P3 R fenv env e.
split.
-intro s.
 unfold hoareTriple_Step.
 intros s0 s' e' H1 [H2 [H3 H4]].
 apply s in H1.
 auto.
-intro s.
 unfold hoareTriple_Step.
 intros s0 s' e' H1 [H2 [H3 H4]].
 apply s in H1.
 auto.
Qed.
(*
split;
intro s;
unfold hoareTriple_Step;
intros s0 s' e' H1 [H2 [H3 H4]];
apply s in H1;
auto.*)

Lemma preAnd:
 forall (P1 Q : W -> Prop) (P2  : Exp -> W -> Prop) (fenv: funEnv) (env: valEnv) (e: Exp),
{{P1}} fenv >> env >> e {{P2}} -> {{fun s => P1 s /\ Q s}} fenv >> env >> e {{P2}}.
Proof.
intros P1 Q P2 fenv env e H s.
intros s' e' H1 [H2 H3].
apply H in H1.
apply H1.
auto.
Qed.

Lemma conjPrePost :
forall (P1 Q1 : W -> Prop) (P2 Q2 : Exp -> W -> Prop) (fenv: funEnv) (env: valEnv) (e : Exp),
{{P1}} fenv >> env >> e {{P2}} ->
{{Q1}} fenv >> env >> e {{Q2}} -> 
{{fun s => P1 s /\ Q1 s}} fenv >> env >> e {{fun a s => P2 a s /\ Q2 a s}}.
Proof.
intros P1 Q1 P2 Q2 fenv env e H1 H2 s.
intros s' e' H3 [H4 H5].
split.
-apply H1 in H3.
 auto.
-apply H2 in H3.
 auto.
Qed.

End HDV1bis.