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
Require Import Hardware_Deep_v2.
Require Import Coq.Logic.EqdepFacts.
Require Import IdModA_M2.

Module Hoare_Test_state <: IdModType.

Module HardwareC := Hardware IdMod.
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


Fixpoint findD {K V: Type} {h: DEq K} (m: list (K * V)) (d: V) (k: K) : V :=
  match m with
     | nil => d
     | cons (k', x) ls => match (dEq k k') with
                            | left _ => x
                            | right _ => findD ls d k
                            end              
    end.

Fixpoint update1 {K V: Type} {h: DEq K} (m: list (K * V)) (k: K) (v: V) :
  list (K * V) :=
  match m with
     | nil => [(k,v)]
     | cons (k', x) ls => match (dEq k k') with
                            | left _ => (k',v):: ls
                            | right _ => (k',x) :: update1 ls k v
                            end              
    end.

Lemma findUpdate {K V: Type} {h: DEq K} : 
forall (m: list (K * V)) (x: K) (v v': V), findD(update1 m x v) v' x = v.
Proof.
intros.
induction m.
simpl.
destruct dEq.
auto.
contradiction.
induction a.
unfold update1.
destruct dEq.
apply symmetry in e.
rewrite e.
simpl.
destruct dEq.
auto.
contradiction.
simpl.
destruct dEq.
contradiction.
auto.
Qed.

Definition xf_read : XFun Id nat := {|
   b_mod := fun s x => (s, findD s 0 x)    
|}.                                                    

Definition xf_write : XFun (Id * nat) unit := {|
   b_mod := fun s x => (update1 s (fst x) (snd x), tt)    
|}.                                                    


(*
Definition xf_reset : XFun (PState W) unit := {|
   b_mod := fun x _ => (b_init, tt)    
|}.
*)                                                 

Instance VT_Id : ValTyp Id.

Instance VT_IdNat : ValTyp (Id * nat).

Definition Read (x: Id) : Exp :=
  Modify Id nat VT_Id NatV xf_read (QV (cst Id x)).

Definition Write (x: Id) (v: nat) : Exp :=
  Modify (Id * nat) unit VT_IdNat UnitV xf_write (QV (cst (Id * nat) (x,v))).

(*Definition Reset (VW: ValTyp (PState W)) : Exp :=
  Modify (PState W) unit VW UnitV xf_reset
         (QV (cst (PState nat) pstate_nat)).*)

(** 1 *)

Lemma write_entry_1 (P0: W -> Prop)
           (fenv: funEnv) (env: valEnv) (x: Id) (v: nat): 
  forall (s s': W) (e: Exp),
    EStep fenv env (Conf Exp s (Write x v))
                      (Conf Exp s' e) ->
  P0 (update1 s x v) -> P0 s'.
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


Definition WriteEntry1SHT (P0: W -> Prop)
                       (fenv: funEnv) (env: valEnv) (x: Id) (v: nat):=
  HoareTriple_Step (fun s => P0 (update1 s x v)) (fun _ s => P0 s) fenv env (Write x v).

Lemma write_entry_1_sht (P0: W -> Prop)
           (fenv: funEnv) (env: valEnv) (x: Id) (v: nat): 
  forall (s s': W) (e: Exp),
    WriteEntry1SHT P0 fenv env x v.
Proof.
intros s s' e.
unfold WriteEntry1SHT.
unfold HoareTriple_Step.
apply write_entry_1.
Qed.

(** 2 *)

Lemma write_entry_2 (P0: W -> Prop)
           (fenv: funEnv) (env: valEnv) (x: Id) (v: nat): 
  forall (s s': W) (e: Exp),
    EStep fenv env (Conf Exp s (Write x v))
                      (Conf Exp s' e) ->
  P0 (update1 s x v) -> P0 s' /\ s' = update1 s x v.
Proof.
intros s s' e H1 H2.
split.
eapply write_entry_1.
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

Definition WriteEntry2SHT (P0: W -> Prop)
                       (fenv: funEnv) (env: valEnv) (x: Id) (v: nat):=
  HoareTriple_Step (fun s => P0 (update1 s x v)) (fun _ s => P0 s)
                   fenv env (Write x v).

Lemma write_Entry_2_sht (P0: W -> Prop)
           (fenv: funEnv) (env: valEnv) (x: Id) (v: nat): 
  forall (s s': W) (e: Exp),
    WriteEntry2SHT P0 fenv env x v.
intros s s' e.
unfold WriteEntry2SHT.
unfold HoareTriple_Step.
eapply write_entry_2.
Qed.

(** 3 *)

Lemma read_entry_1 (P0: Value -> Prop)
           (fenv: funEnv) (env: valEnv) (x: Id): 
  forall (s s': W) (v: Value),
    EClosure fenv env (Conf Exp s (Read x))
             (Conf Exp s' (Val v)) ->
    P0 (cst nat (findD s 0 x)) -> P0 v.
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



Definition ReadEntry1SHT (P0: Value -> Prop)
                       (fenv: funEnv) (env: valEnv) (x: Id):=
  HoareTriple_Step (fun s => P0 (cst nat (findD s 0 x)))
                   (fun e _ => forall v: Value,
                                 e = Val v -> P0 v) fenv env (Read x).

Definition ReadEntry1VHT (P0: Value -> Prop)
                       (fenv: funEnv) (env: valEnv) (x: Id) :=
  HoareTriple_Eval (fun s => P0 (cst nat (findD s 0 x)))
                   (fun v _ => P0 v) fenv env (Read x).


(** 4 *)

Lemma read_entry_2 (P0: Value -> Prop)
           (fenv: funEnv) (env: valEnv) (x: Id): 
  forall (s s': W) (v: Value),
    EClosure fenv env (Conf Exp s (Read x))
             (Conf Exp s' (Val v)) ->
    P0 (cst nat (findD s 0 x)) -> P0 v /\ v = (cst nat (findD s' 0 x)).
Proof.
intros s s' v H1 H2.
eauto.
split.
eapply read_entry_1.
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


Definition ReadEntry2SHT (P0: Value -> Prop)
                       (fenv: funEnv) (env: valEnv) (x: Id):=
  HoareTriple_Step (fun s => P0 (cst nat (findD s 0 x)))
                   (fun e s => forall v: Value,
                          e = Val v -> P0 v /\ v = cst nat (findD s 0 x)) fenv env (Read x).

Definition ReadEntry2VHT (P0: Value -> Prop)
                       (fenv: funEnv) (env: valEnv) (x: Id):=
  HoareTriple_Eval (fun s => P0 (cst nat (findD s 0 x)))
                   (fun v s => P0 v /\ v = cst nat (findD s 0 x)) fenv env (Read x).



(** 5 *)

Lemma wread_entry_1 (P0: Value -> Prop)
           (fenv: funEnv) (env: valEnv) (x: Id) (n: nat): 
  forall (s s': W) (v: Value),
    EClosure fenv env (Conf Exp s (BindN (Write x n) (Read x)))
                      (Conf Exp s' (Val v)) ->
  P0 (cst nat n) -> P0 v.
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
rewrite findUpdate.
auto.
inversion X6.
inversion X6.
inversion X4.
inversion X2.
Qed.


Definition WReadEntry1EHT (P0: Value -> Prop)
           (fenv: funEnv) (env: valEnv) (x: Id) (n:nat) :=
  HoareTriple_ExtendedStep (fun _ => P0 (cst nat n))
                           (fun e _ => forall v: Value, e = Val v -> P0 v)
                           fenv env (BindN (Write x n) (Read x)).

Lemma wread_nat_1_eht (P0: Value -> Prop)
      (fenv: funEnv) (env: valEnv) (x: Id) (n:nat):
    WReadEntry1EHT P0 fenv env x n.
Proof.
unfold WReadEntry1EHT.
unfold HoareTriple_ExtendedStep.
intros s s' e' H1 H2 v H3.
eapply wread_entry_1.
rewrite <- H3.
eauto. auto.
Qed.


Definition WReadEntry1VHT (P0: Value -> Prop)
           (fenv: funEnv) (env: valEnv) (x: Id) (n:nat):=
  HoareTriple_Eval (fun _ => P0 (cst nat n))
                    (fun v _ => P0 v)
                    fenv env (BindN (Write x n) (Read x)).
 
Lemma wread_entry_1_vht (P0: Value -> Prop)
      (fenv: funEnv) (env: valEnv) (x: Id) (n:nat):
    WReadEntry1VHT P0 fenv env x n.
Proof.
unfold WReadEntry1VHT.
unfold HoareTriple_Eval.
eapply wread_entry_1.
Qed.

(** 6 *)

Lemma wread_entry_2 (P0: Value -> Prop)
           (fenv: funEnv) (env: valEnv) (x: Id) (n:nat): 
  forall (s s': W) (v: Value),
    EClosure fenv env (Conf Exp s (BindN (Write x n) (Read x)))
                      (Conf Exp s' (Val v)) ->
  P0 (cst nat n) -> P0 v /\ (update1 s x n) = s' /\ v = cst nat n. 
Proof.
intros s s' v H1 H2.
split.
eapply wread_entry_1.
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
 repeat apply inj_pair2 in H12.
 apply symmetry in H12.
 rewrite H12.
 rewrite findUpdate.
 auto.
 inversion X9;subst.
 inversion X9.
 inversion X7;subst.
 inversion X7.
 inversion X2.
Qed.


Definition WReadEntry2VHT (P0: Value -> Prop)
           (fenv: funEnv) (env: valEnv) (x: Id) (n:nat):=
  HoareTriple_Eval (fun _ => P0 (cst nat n))
                    (fun v s => P0 v /\ v = cst nat n)
                    fenv env (BindN (Write x n) (Read x)).
 
Lemma wread_entry_2_vht (P0: Value -> Prop)
      (fenv: funEnv) (env: valEnv) (x: Id) (n:nat):
    WReadEntry2VHT P0 fenv env x n.
Proof.
unfold WReadEntry2VHT.
unfold HoareTriple_Eval.
intros.
split.
eapply wread_entry_2.
eauto.
auto.
eapply wread_entry_2.
eauto.
eauto.
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

End Hoare_Test_state.

