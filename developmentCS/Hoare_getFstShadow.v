Require Export EnvLibA.
Require Export RelLibA.
Require Export PRelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Import StaticSemA.
Require Import DynamicSemA.
Require Import TRInductA.
Require Import WeakenA.
Require Import TSoundnessA.
Require Import IdModTypeA.
Require Import IdModPip.
Require Import DetermA.
Require Import AbbrevA.
Require Import HoareA.
Require Import THoareA.
Require Import Lib.
Require Import Pip_state.
Require Import Pip_stateLib.
Require Import Coq.Structures.Equalities.

Module Hoare_Test_FstShadow <: IdModType.

Module FstShadow := THoare IdModP.
Export FstShadow.

Definition Id := FstShadow.Id.
Definition IdEqDec := FstShadow.IdEqDec.
Definition IdEq := FstShadow.IdEq.
Definition W := FstShadow.W.
Definition Loc_PI := FstShadow.Loc_PI.
Definition BInit := FstShadow.BInit.
Definition WP := FstShadow.WP.

(**************************************************)

(******* Program *)

(** getSh1idx : returns first shadow *)

Definition getSh1idx : Exp := Val (cst index sh1idx). (** Return in the original definition *)

(** ReadPhysical -page -index : reads physical address *)

Definition xf_read (p: page) : XFun (option index) (option page) := {|
   b_mod := fun s oi => (s,match oi with |None => None |Some i => readPhysicalInternal p i (memory s) end)
|}.

Instance VT_index : ValTyp index.
Instance VT_option_index : ValTyp (option index).
Instance VT_option_page : ValTyp (option page).

Definition ReadPhysical (p:page) (x:Id) : Exp :=
  Modify (option index) (option page) VT_option_index VT_option_page (xf_read p) (Var x).  

(** Succ -index : calculates the successor of an index *)                 

Definition xf_succ : XFun index (option index) := {|
   b_mod := fun s (idx:index) =>  (s, succIndexInternal idx)
|}.

Definition Succ (x:Id) : Exp :=
  Modify index (option index) VT_index VT_option_index xf_succ (Var x).

(** getFstShadow -page : returns the adress of the 1st shadow *)

Definition getFstShadow (p:page) : Exp :=
 BindS "x" getSh1idx 
           (BindS "y" (Succ "x") 
                      (ReadPhysical p "y")
           ).


(******* State properties *)

Definition isVA (p:page) (i:index) (s:W): Prop := match (lookup p i (s.(memory)) beqPage beqIndex) with 
             |Some (VA _) => True
             |_ => False
             end.

Definition nextEntryIsPP (p:page) (idx:index) (p':Value) (s:W) : Prop:= 
match succIndexInternal idx with 
| Some i => match lookup p i (memory s) beqPage beqIndex with 
                  | Some (PP table) => p' = cst (option page) (Some table)
                  |_ => False 
                  end
| _ => False 
end.

Definition partitionDescriptorEntry (s:W) := 
forall (p : page),  
  In p (getPartitions multiplexer s)-> forall (idx : index), 
    (idx = PDidx \/ idx = sh1idx \/ idx = sh2idx \/ idx = sh3idx \/ idx = PPRidx  \/ idx = PRidx ) ->
    idx < tableSize - 1  /\ isVA p idx  s /\ exists (p1:page) , nextEntryIsPP p idx (cst (option page) (Some p1)) s  /\  
    (cst page p1) <> (cst page defaultPage).


(******* Useful Lemmas *)

(** about getSh1idx *)

Lemma getSh1idxW (P: Value -> W -> Prop) (fenv: funEnv) (env: valEnv) :
  {{wp P fenv env getSh1idx}} fenv >> env >> getSh1idx {{P}}.
Proof.
apply wpIsPrecondition.
Qed.

Lemma getSh1idxWp P fenv env :
{{fun s => P s }} fenv >> env >> getSh1idx 
{{fun (idxSh1 : Value) (s : state) => P s  /\ idxSh1 = cst index sh1idx }}.
Proof.
eapply weakenEval.
eapply getSh1idxW.
intros. 
unfold wp.
intros.
unfold getSh1idx in X.
inversion X;subst.
auto.
inversion X0.
Qed.

(** about Succ *)

Require Import Coq.Logic.Eqdep.

Lemma succW  (x : Id) (P: Value -> W -> Prop) (v:Value) (fenv: funEnv) (env: valEnv) :
forall (idx:index), {{fun s => idx < (tableSize -1) /\ forall  l : idx + 1 < tableSize , 
    P (cst (option index) (succIndexInternal idx)) s /\ v = cst index idx }}  
fenv >> (x,v)::env >> Succ x {{ P }}.
Proof.
intros.
unfold THoareTriple_Eval.
intros.
intuition.
destruct H1 as [H1 H1'].
omega.
inversion X;subst.
inversion X0;subst.
repeat apply inj_pair2 in H7;subst.
inversion X2;subst.
inversion X3;subst.
inversion H;subst.
destruct IdModP.IdEqDec in H3.
inversion H3;subst.
clear H3 e X3 H XF1.
inversion X1;subst.
inversion X3;subst.
repeat apply inj_pair2 in H7.
repeat apply inj_pair2 in H9.
subst.
unfold b_exec,b_eval,xf_succ,b_mod in *.
simpl in *.
inversion X4;subst.
apply H1.
inversion X5.
inversion X5.
contradiction.
Qed.

Lemma succWp (x:Id) (v:Value) P (fenv: funEnv) (env: valEnv) :
forall (idx:index), {{fun s => P s  /\ idx < tableSize - 1 /\ v=cst index idx}} fenv >> (x,v)::env >> Succ x 
{{fun (idxsuc : Value) (s : state) => P s  /\ exists i, idxsuc = cst (option index) (Some i)}}.
Proof.
intros.
eapply weakenEval.
eapply succW.
intros.
simpl.
split.
instantiate (1:=idx).  
intuition.
intros.
intuition.
destruct idx.
exists (CIndex (i + 1)).
f_equal.
unfold succIndexInternal.
case_eq (lt_dec i tableSize).
intros.
auto.
intros.
contradiction.
Qed.

(******* about readPhysical *)

Lemma readPhysicalW (y:Id) table (v:Value) (P' : Value -> W -> Prop) (fenv: funEnv) (env: valEnv) :
 {{fun s =>  exists idxsucc p1, v = cst (option index) (Some idxsucc)
              /\ readPhysicalInternal table idxsucc (memory s) = Some p1 
              /\ P' (cst (option page) (Some p1)) s}} 
fenv >> (y,v)::env >> ReadPhysical table y {{P'}}.
Proof.
intros.
unfold THoareTriple_Eval.
intros.
intuition.
destruct H.
destruct H.
intuition.
inversion H0;subst.
clear k3 t k2 k1 ftenv tenv H1.
inversion X;subst.
inversion X0;subst.
repeat apply inj_pair2 in H7.
subst.
inversion X2;subst.
inversion X3;subst.
inversion H0;subst.
destruct IdEqDec in H3.
inversion H3;subst.
clear H3 e X3 H0 XF1. 
inversion X0;subst.
repeat apply inj_pair2 in H7.
repeat apply inj_pair2 in H11.
subst.
inversion X1;subst.
inversion X4;subst.
repeat apply inj_pair2 in H7.
apply inj_pair2 in H9.
subst.
unfold xf_read at 2 in X4.
unfold b_eval,b_exec,b_mod in X4.
simpl in *.
rewrite H in X4.
unfold xf_read,b_eval,b_exec,b_mod in X5.
simpl in *.
rewrite H in X5.
inversion X5;subst.
auto.
inversion X6.
inversion X6.
contradiction.
Qed.


(** Hoare Triple *)

Lemma getFstShadow1 (partition : page) (P : W -> Prop) (fenv: funEnv) (env: valEnv) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ In partition (getPartitions multiplexer s)}}
fenv >> env >> (getFstShadow partition) 
{{fun (sh1 : Value) (s : state) => P s /\ nextEntryIsPP partition sh1idx sh1 s}}.
Proof.
unfold getFstShadow.
eapply BindS_VHTT1.
eapply getSh1idxWp.
simpl; intros.
eapply BindS_VHTT1.
eapply weakenEval.
eapply succW. simpl.
simpl; intros; intuition.
instantiate (1:=sh1idx).
eapply H0 in H3.
specialize H3 with sh1idx.
eapply H3.
auto.
instantiate (1:=(fun v0 s => P s /\ partitionDescriptorEntry s /\ 
                          In partition (getPartitions multiplexer s) /\ 
                          exists i, succIndexInternal sh1idx = Some i /\ v0 = cst (option index) (Some i) )).
simpl.
intuition.
exists (CIndex (sh1idx+1)).
f_equal.
unfold succIndexInternal.
unfold sh1idx.
unfold CIndex.
case_eq (lt_dec 4 tableSize).
intros.
simpl.
case_eq (lt_dec 4 tableSize).
intros.
case_eq (lt_dec 5 tableSize).
intros.
auto.
intros.
auto.
contradiction.
intros.
destruct index_d.
case_eq (lt_dec i tableSize).
intros.
simpl.
auto.
contradiction.
auto. 
simpl; intros.
eapply weakenEval.
eapply readPhysicalW.
simpl;intros.
intuition.
destruct H3.
exists x.
unfold partitionDescriptorEntry in H.
apply H with partition sh1idx in H1.
clear H.
intuition.
destruct H5.
exists x0.
intuition.
unfold nextEntryIsPP in H5.
unfold readPhysicalInternal.
rewrite H1 in H5.
destruct (lookup partition x (memory s) beqPage beqIndex).
unfold cst in H5.
destruct v1;try contradiction.
apply inj_pairT2 in H5.
inversion H5.
auto.
unfold isVA in H2.
destruct (lookup partition sh1idx (memory s) beqPage beqIndex) in H2;try contradiction.
auto.
Qed.


End Hoare_Test_FstShadow.
