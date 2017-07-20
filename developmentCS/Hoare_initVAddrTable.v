Require Export EnvLibA.
Require Export RelLibA.
Require Export PRelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega Bool Coq.Logic.ProofIrrelevance.
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
Require Import Coq.Logic.Eqdep.
Require Import Hoare_getFstShadow.
Require Import Hoare_writeVirtualInv.
Require Import Pip_DependentTypeLemmas.
Require Import Pip_InternalLemmas.
Require Import Pip_Prop.
Import ListNotations.

Module Hoare_Test_SndShadow.

Module SndShadow := Hoare_Test_VirtualInv.
Export SndShadow.

(**************************************************)

(******* Program *)

Axiom tableSizeNotZero : tableSize <> 0.

Instance VT_nat : ValTyp nat.
Instance VT_bool : ValTyp bool.
Instance PageVT : ValTyp page.
Definition Page := vtyp page.
Instance indexVT : ValTyp index.
Definition Index := vtyp index.

Definition maxIndex : index := CIndex(tableSize-1). 

Definition xf_Ltb (i:index) : XFun index bool := {|
   b_mod := fun s idx => (s,Index.ltb idx i)
|}.

Definition LtLtb (x:Id) (i:index) : Exp :=
  Modify index bool VT_index VT_bool (xf_Ltb i) (Var x). 
 
Definition xf_ExtractIndex : XFun (option index) index := {|
   b_mod := fun s idx => (s,match idx with |Some i => i |_ => index_d end)
|}.

Definition ExtractIndex (x:Id):= 
  Modify (option index) index VT_option_index VT_index xf_ExtractIndex (Var x). 

Definition xf_writeVirtual' (p: page) (v: vaddr) : XFun index unit := {|
   b_mod := fun s i => (writeVirtualInternal p i v s,tt)
|}.

Definition WriteVirtual' (p: page) (i: Id) (v: vaddr) : Exp :=
  Modify index unit VT_index VT_unit (xf_writeVirtual' p v) (Var i).

Definition initVAddrTableAux (f i: Id) (p:page) : Exp :=
BindN (WriteVirtual' p i defaultVAddr)
      (IfThenElse (LtLtb i maxIndex)
                  (BindS "y" (BindS "idx" (SuccD i) 
                                          (ExtractIndex "idx")
                             )
                             (Apply (FVar f) 
                                    (PS [VLift(Var "y")])
                             )
                  )
                  (Val (cst unit tt))
      ). 

Definition initVAddrTable (p:page) (i:index) := 
Apply
(QF  (FC emptyE [("x",Index)] (Val (cst unit tt)) (initVAddrTableAux "initVAddrTable" "x" p) "initVAddrTable" tableSize))
(PS[Val (cst index i)]).

(******* Useful Lemmas *)


Lemma removeDupIdentity  (l :  list (paddr * value)) : 
forall table1 idx1 table2 idx2 , table1 <> table2 \/ idx1 <> idx2 -> 
lookup table1 idx1 (removeDup table2 idx2 l  beqPage beqIndex) beqPage beqIndex = 
lookup table1 idx1 l beqPage beqIndex.
Proof.
intros.
induction l.
simpl. trivial.
simpl.
destruct a.
destruct p.
apply beqPairsFalse in H.
+ case_eq (beqPairs (p, i) (table2, idx2) beqPage beqIndex).
  - intros.
    unfold beqPairs in H0. cbn in H0.
    case_eq (beqPage p table2 && beqIndex i idx2 ).
    * intros.
      rewrite H1 in H0.
      unfold beqPage , beqIndex in H1.
      apply andb_true_iff in H1.
      destruct H1.
      apply beq_nat_true in H1.
      apply beq_nat_true in H2.
      assert (beqPairs (p, i) (table1, idx1) beqPage beqIndex = false).
      { destruct p, i, table2, table1, idx2, idx1. simpl in *.
      subst.
      assert (Hp = Hp0). apply proof_irrelevance. subst. 
      assert(Hi = Hi0).  apply proof_irrelevance. subst.
      unfold beqPairs in *. cbn in *.
      
      rewrite NPeano.Nat.eqb_sym.
      replace (i0 =? i1) with (i1 =? i0). assumption.
      rewrite NPeano.Nat.eqb_sym . trivial. }
      rewrite H3. assumption.
    * intros. rewrite H1 in H0.
      contradict H0. auto.
  - intros. simpl. 
    case_eq (beqPairs (p, i) (table1, idx1) beqPage beqIndex).
    intros. trivial.
    intros. assumption.   
Qed.

Lemma succDWp' (x:Id) (v:Value) P (fenv: funEnv) (env: valEnv) :
forall (idx:index), {{fun s => P s  /\ idx < tableSize - 1 /\ v=cst index idx}} fenv >> (x,v)::env >> SuccD x 
{{fun (idxsuc : Value) (s : state) => P s  /\ idx < tableSize - 1 /\ v=cst index idx /\ idxsuc = cst (option index) (succIndexInternal idx) /\ exists i, idxsuc = cst (option index) (Some i)}}.
Proof.
intros.
eapply weakenEval.
eapply succDW.
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

Definition THoareFunTriple_Eval
      (P: W -> Prop) (Q: Value -> W -> Prop) 
      (fenv: funEnv) (env: valEnv)
      (qf: QFun) : Prop :=
  forall (ftenv: funTC)
         (k1: FEnvTyping fenv ftenv)
         (ft: FTyp)
         (k2: QFunTyping ftenv fenv qf ft)
         (s s': W) (f: Fun),
  QFClosure fenv (Conf QFun s qf) (Conf QFun s' (QF f)) ->
  match f with
    | FC fenv' tenv' e0 e1 x n => 
    EnvTyping env tenv' ->  
    match n with
      | 0 =>       
        THoareTriple_Eval P Q fenv' env e0
      | S n' =>       
          THoareTriple_Eval P Q ((x,FC fenv' tenv' e0 e1 x n')::fenv') env e1
       (*forall envG, THoareTriple_Eval P Q fenv envG (BindMS ((x,FC fenv' tenv' e0 e1 x (S n'))::fenv') env e1)*)
    end
  end.


Lemma Apply_VHTT2 (P0: W -> Prop) (P1: list Value -> W -> Prop)
                 (P2: Value -> W -> Prop) 
   (fenv: funEnv) (env: valEnv) (qf: QFun) (es: list Exp) :
  THoarePrmsTriple_Eval P0 P1 fenv env (PS es) ->
  (forall env, THoareFunTriple_Eval (P1 (map snd env)) P2 fenv env qf) -> 
   THoareTriple_Eval P0 P2 fenv env (Apply qf (PS es)).
Admitted.

Lemma BindMS_VHTT1 (P1: W -> Prop)
                 (P2: Value -> W -> Prop) 
   (fenv fenv': funEnv) (env env': valEnv) e :
          THoareTriple_Eval P1 P2 (fenv'++fenv) (env'++env) e ->
          THoareTriple_Eval P1 P2 fenv env (BindMS fenv' env' e).
Admitted.

Lemma BindMS_VHTT2 (P1: W -> Prop)
                 (P2: Value -> W -> Prop)  
   (fenv: funEnv) (env: valEnv) e : 
          THoareTriple_Eval P1 P2 fenv env e ->
          forall fenv' env', THoareTriple_Eval P1 P2 fenv' env' (BindMS fenv env e).
Admitted.




(******* Hoare Triple *)

Lemma initVAddrTableNewProperty table (curidx : index) (fenv: funEnv) (env: valEnv) :
{{ fun s => (forall idx : index, idx < curidx -> 
(readVirtual table idx (memory s) = Some defaultVAddr) )}} 
fenv >> env >> initVAddrTable table curidx 
{{fun _ s => forall idx, readVirtual table  idx s.(memory) = Some defaultVAddr  }}.
Proof.
unfold initVAddrTable.
unfold initVAddrTableAux.
eapply Apply_VHTT2.
(** begin PS [Val (cst index curidx)] *)
instantiate (1:= fun vs s => (forall idx : index,
   idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) 
      /\ vs = [cst index curidx] ).
unfold THoarePrmsTriple_Eval.
intros.
inversion X;subst.
destruct vs; inversion H5.
destruct vs ; inversion H2 ; subst.
intuition.
inversion X0;subst.
inversion X2.
inversion X2.
(** end *)
intros vs ; simpl.
unfold THoareFunTriple_Eval;intros.
inversion X;subst.
Focus 2. inversion X0.
revert vs.
assert(H : tableSize + curidx >= tableSize) by omega.
revert H k2.
revert curidx.
generalize tableSize at 1 3 4. 
induction n.  simpl. 
(** begin case n=0 *)
intros.
destruct curidx.
simpl in *.
omega.
(** end *)
intros;simpl.
destruct vs.
unfold THoareTriple_Eval;intros.
intuition; inversion H2.
destruct vs.
Focus 2.
unfold THoareTriple_Eval;intros.
intuition; inversion H2.
destruct p.
simpl in *.
inversion X0;subst.
clear X1 H1.
(*eapply BindMS_VHTT1.*)
eapply BindN_VHTT1.
(** Begin write Virtual *)
unfold THoareTriple_Eval.
intros.
clear X0 X IHn k4 k3 k2 k1 k0 t ft ftenv ftenv0 tenv env.
rename X1 into X.
intuition.
inversion H2;subst.
inversion X;subst.
inversion X1;subst.
inversion X0;subst.
inversion X0;subst.
repeat apply inj_pair2 in H8.
subst.
inversion X4;subst.
inversion X5;subst.
simpl in *.
inversion H0;subst.
clear X5 H0 XF1.
inversion X2;subst.
repeat apply inj_pair2 in H8.
repeat apply inj_pair2 in H10.
subst.
unfold b_exec, b_eval, b_mod in *.
simpl in *.
inversion X3;subst.
clear X0 X X1 X2 X3 X4.
instantiate (1:= fun s => (forall idx : index,
     idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\ 
    v = cst index curidx /\ readVirtual table curidx s.(memory) = Some defaultVAddr).
intuition.
split.
intros.
unfold writeVirtualInternal.
simpl.
unfold readVirtual.
unfold add.
simpl.
assert(Hfalse : Lib.beqPairs (table, curidx) (table, idx) beqPage beqIndex= false).
    { apply beqPairsFalse. 
      right.
      apply indexDiffLtb.
      right;assumption. }
    rewrite Hfalse.
assert (lookup  table idx (Lib.removeDup table curidx (memory n') beqPage beqIndex)
           beqPage beqIndex = Lib.lookup  table idx  (memory n') beqPage beqIndex) as Hmemory.
    { apply removeDupIdentity.
      right. 
      apply indexDiffLtb.
      left; trivial. }
rewrite Hmemory.
apply H1 in H0.
unfold readVirtual in *. auto. 
intuition.
unfold writeVirtualInternal.
simpl.
unfold readVirtual.
unfold add.
simpl.
assert(Htrue : Lib.beqPairs (table, curidx) (table, curidx) beqPage beqIndex= true).
    { apply beqPairsTrue.
      intuition. }
rewrite Htrue.
auto.
inversion X5.
inversion X5.
(** end *)
eapply IfTheElse_VHTT1.
(** begin LtLtb *)
unfold THoareTriple_Eval.
clear X IHn k2 k1 ft env ftenv X0.
intros.
clear k3 k2 k1 t tenv ftenv.
intuition.
subst.
inversion X;subst.
inversion X0;subst.
repeat apply inj_pair2 in H8.
subst.
inversion X2;subst.
inversion X3;subst.
simpl in *.
inversion H0;subst.
clear X3 H0 XF1.
inversion X1;subst.
inversion X3;subst.
repeat apply inj_pair2 in H8.
repeat apply inj_pair2 in H10.
subst.
unfold b_eval, b_exec, xf_Ltb, b_mod in *.
simpl in *.
inversion X4;subst.
instantiate (1:= fun b s =>
  (forall idx : index,
   idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\
    readVirtual table curidx (memory s) = Some defaultVAddr /\ v = cst index curidx /\ b = cst bool (Index.ltb curidx maxIndex)).
intuition.
inversion X5.
inversion X5.
(** end *)
simpl.
eapply BindS_VHTT1.
eapply BindS_VHTT1.
clear IHn X k2 k1 ft env ftenv X0.
(** begin SuccD *)
eapply weakenEval.
instantiate (2:= fun s => (fun s' => (forall idx : index,
 idx < curidx -> readVirtual table idx (memory s') = Some defaultVAddr) 
      /\ readVirtual table curidx (memory s) = Some defaultVAddr) s /\
      curidx < tableSize - 1 /\ v=cst index curidx).
eapply succDWp'.
simpl;intros; intuition.
unfold maxIndex in H4.
inversion H4.
apply inj_pair2 in H5.
symmetry in H5.
apply indexltbTrue in H5.
unfold CIndex in H5.
destruct (lt_dec (tableSize - 1) tableSize). 
simpl in *.  
assumption.
contradict n0.
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
omega.
(** end *) 
(** begin ExtractIndex *)
intros;simpl.
clear IHn X k2 k1 ft env ftenv X0.
instantiate (1:= fun v' s => (forall idx : index,
   idx < curidx -> readVirtual table idx (memory s) = Some defaultVAddr) /\
   readVirtual table curidx (memory s) = Some defaultVAddr /\
  v = cst index curidx /\ curidx < tableSize - 1 /\
  v' = cst index (match succIndexInternal curidx with | Some i => i | None => index_d end) ).
unfold THoareTriple_Eval.
intros.
clear k3 k2 k1 t tenv ftenv.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
subst.
destruct H4.
inversion H2.
repeat apply inj_pair2 in H4.
rewrite H4 in *.
inversion X;subst.
inversion X0;subst.
repeat apply inj_pair2 in H10.
subst.
inversion X2;subst.
inversion X3;subst.
simpl in *.
inversion H3;subst.
clear X3 H3 XF1.
inversion X1;subst.
inversion X3;subst.
repeat apply inj_pair2 in H10.
repeat apply inj_pair2 in H12.
subst.
unfold b_eval, b_exec, xf_ExtractIndex, b_mod in *.
simpl in *.
inversion X4;subst.
intuition.
inversion X5.
inversion X5.
(** end *)
intros; simpl.
clear X.
(** recursive call *)
unfold THoareTriple_Eval.
intros.
intuition.
subst.
unfold succIndexInternal in *.
destruct curidx.
simpl in *.
case_eq (lt_dec i tableSize);intros; try contradiction.
rewrite H2 in *. 
specialize (IHn (CIndex(i+1))).
unfold CIndex in *.
case_eq (lt_dec (i + 1) tableSize);intros.
rewrite H4 in *.
simpl in *.
assert (Z : n+(i+1) = S(n+i)) by omega.
rewrite Z in *.
eapply IHn in H as H5.
clear IHn.
destruct n eqn:B.
omega.
eapply H5.
(*eapply k0.
eapply k3.
repeat (try econstructor; simpl; eauto).*)
admit.
admit.
admit.
clear  H4 H3 H2 H5 H0 k4 k3 k2 k1 k0.
instantiate (1:=v1).
inversion X;subst.
inversion X1;subst.
inversion X3;subst.
inversion X4;subst.
inversion H0;subst.
clear X4 H0.
inversion X2;subst.
inversion X4;subst.
inversion H12;subst.
destruct vs; inversion H0.
inversion X6;subst.
inversion X7;subst.
inversion X8;subst.
inversion X9;subst.
inversion H0;subst.
clear X9 H0.
inversion X5;subst.
inversion X9;subst.
inversion H12;subst.
destruct vs; inversion H0.
inversion X11;subst.
inversion X12;subst.
inversion X10;subst.
inversion X13;subst.
inversion H12;subst.
destruct vs; inversion H0;subst.
destruct vs; inversion H4;subst.
clear H4 H0 H13.
unfold mkVEnv in *.
simpl in *.
admit.
eauto.
inversion X15;subst.
inversion X16.
inversion X16.
inversion X15.
inversion X13.
inversion X11.
inversion X6.
clear X0 X H5 H k4 k3 k2 k1 k0 t ft ftenv ftenv0 tenv env idx.
intuition; simpl in *.
 assert (Hor : idx = {| i := i; Hi := Hi |} \/ idx < {| i := i; Hi := Hi |}).
    { simpl in *.
      unfold CIndex in H.
      destruct (lt_dec (i + 1) tableSize).
      subst.
      simpl in *.
      rewrite NPeano.Nat.add_1_r in H.
      apply lt_n_Sm_le in H.
      apply le_lt_or_eq in H.
      destruct H.
      right. assumption.
      left. subst.
      destruct idx. simpl in *.
      subst. 
      assert (Hi = Hi0).
      apply proof_irrelevance.
      subst. reflexivity. omega. }
destruct Hor.
subst.
assumption.
apply H1;trivial.
do 3 econstructor; simpl; auto.
induction n; simpl in *;
assert (i+1<tableSize) by omega;
contradiction.
(** false case*)
revert H.
clear;intros.
unfold mkVEnv in *.
simpl in *.
unfold THoareTriple_Eval.
intros.
intuition.
clear k3 k2 k1 ftenv tenv.
inversion X;subst.
Focus 2. inversion X0.
inversion H4.
repeat apply inj_pair2 in H3.
clear X H4.
assert (idx < CIndex (tableSize - 1) \/ idx = CIndex (tableSize - 1)).
    { destruct idx. simpl in *. 
      unfold CIndex.
      case_eq (lt_dec (tableSize - 1) tableSize).
      intros. simpl in *.
      assert (i <= tableSize -1).
      omega.
      apply NPeano.Nat.le_lteq in H4.
      destruct H4.
      left. assumption. right.
      subst.
      assert (Hi =  Pip_state.CIndex_obligation_1 (tableSize - 1) l).
      apply proof_irrelevance.
      subst. reflexivity.
      intros.
      omega. }
destruct H2.
symmetry in H3.
apply indexltbFalse in H3.
generalize (H1 idx);clear H;intros Hmaxi.
apply Hmaxi. subst.
apply indexBoundEq in H3.
subst.
assumption.
symmetry in H3.
apply indexltbFalse in H3.
apply indexBoundEq in H3.
subst.
assumption.
(** end *)
Qed.




End Hoare_Test_SndShadow.
