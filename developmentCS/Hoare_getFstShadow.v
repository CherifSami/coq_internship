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
Import List.ListNotations.

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

Definition readPhysicalInternal p i memory :option page := 
match (lookup p i memory beqPage beqIndex) with
                            | Some (PP a) => Some a
                            | _ => None
                       end.

Definition xf_read (p: page) : XFun index (option page) := {|
   b_mod := fun s i => (s,readPhysicalInternal p i (memory s))
|}.                                  

Instance VT_index : ValTyp index.
Instance VT_option_page : ValTyp (option page).

Definition ReadPhysical (p:page) (x:Id) : Exp :=
  Modify index (option page) VT_index VT_option_page (xf_read p) (Var x).  

(** Succ -index : calculates the successor of an index *)                 

Definition succIndexInternal (idx:index) : option index :=
let (i,P):=idx in 
  if lt_dec i tableSize 
  then Some (CIndex i) 
  else None.

Definition xf_succ : XFun index (option index) := {|
   b_mod := fun s (idx:index) =>  (s, succIndexInternal idx)
|}.

Instance VT_option_index : ValTyp (option index).

Definition Succ (x:Id) : Exp :=
  Modify index (option index) VT_index VT_option_index xf_succ (Var x).

(** getFstShadow -page : returns the adress of the 1st shadow *)

Definition getFstShadow (p:page) : Exp :=
 BindS "x" getSh1idx 
           (BindS "y" (Succ "x") 
                      (ReadPhysical p "y")
           ).

(******* getPartitions from StateLib *)

Fixpoint getAllIndicesAux (pos count: nat) : list index :=
  match count with
    | 0        => []
    | S count1 => match lt_dec pos tableSize with
                   | left pf => Build_index pos pf :: getAllIndicesAux (S pos) count1
                   | _       => []
                 end
  end.

(** The [getAllIndicesAux] function returns the list of all indices  *)
Definition getAllIndices := getAllIndicesAux 0 tableSize.

Fixpoint getAllVAddrAux (levels: nat) : list (list index) :=
  match levels with
    | 0         => [[]]
    | S levels1 => let alls := getAllVAddrAux levels1 in
                  flat_map (fun (idx : index) => map (cons idx) alls) getAllIndices
  end.

(** The [getAllVAddr] function returns the list of all virtual addresses *)
Definition getAllVAddr := map CVaddr (getAllVAddrAux (S nbLevel)).

(**  The [getPd] function returns the physical page of the page directory of
     a given partition  *)
Definition getPd partition memory: option page:= 
match succIndexInternal PDidx with 
|None => None
|Some idx => readPhysicalInternal partition idx memory
end. 


(** The [getNbLevel] function returns the number of translation levels of the MMU *) 
Definition getNbLevel : option level:=
if gt_dec nbLevel 0
then Some (CLevel (nbLevel-1))
else None.

(** The [filterOption] function Remove option type from list *)
Fixpoint filterOption (l : list (option page)) := 
match l with 
| [] => []
| Some a :: l1 => a:: filterOption l1
|None :: l1 => filterOption l1
end.

Definition getIndexOfAddr (va : vaddr) (l : level) : index:=
nth ((length va) - (l + 2))  va (CIndex 0) .

Definition eqbLevel (a b : level) : bool:= a =? b.

Program Definition predLevel (n : level) : option level := 
if gt_dec n 0 then
let ipred := n-1 in 
Some (Build_level ipred _ )
else  None.
Next Obligation.
destruct n.
simpl.
omega.
Qed.

(** The [readPhyEntry] function returns the physical page stored into a given table 
    at a given position in memory. The table should contain only Physical entries 
    (The type [PE] is already defined in [Model.ADT]) *)
Definition readPhyEntry(paddr : page) (idx : index) memory: option page :=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (PE a) => Some a.(pa)
  | Some _ => None
  | None => None
 end. 

(** The [getIndirection] function returns the configuration table entry that corresponds 
    to the given level and virtual address *)
Fixpoint  getIndirection (pd : page) (va : vaddr) (currentlevel : level) (stop : nat) s :=
match stop with 
|0 => Some pd 
|S stop1 => 
if (eqbLevel currentlevel fstLevel)  
then Some pd 
  else  
    let idx :=  getIndexOfAddr va currentlevel in 
       match readPhyEntry pd idx s.(memory) with 
       | Some addr =>  if  defaultPage =? addr 
                          then Some defaultPage 
                          else 
                            match predLevel currentlevel with
                            |Some p =>  getIndirection addr va p stop1 s
                            |None => None
                            end
      |None => None
    end
   end. 

(** The [readPresent] function returns the flag value stored into a given table 
    at a given position in memory. The table should contain only Physical entries 
    (The type [PE] is already defined in [Model.ADT]) *)
Definition readPresent  (paddr : page) (idx : index) memory : option bool:=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (PE a) => Some a.(present)
  | Some _ => None
  | None => None
 end. 

(** The [getMappedPage] function returns the physical page stored into a leaf node, 
   which corresponds to a given virtual address, if the present flag is equal to true **)
Definition getMappedPage pd s va: option page :=
match getNbLevel  with 
 |None => None
 |Some level => let idxVA := getIndexOfAddr va fstLevel  in 
               match getIndirection pd va level (nbLevel - 1) s with 
                | Some tbl =>  if defaultPage =? tbl
                                   then None 
                                   else match (readPresent tbl idxVA s.(memory)) with 
                                         |Some true => readPhyEntry tbl idxVA s.(memory) 
                                         | _ =>  None 
                                        end
                | _ => None
               end
end.


(** The [getMappedPagesOption] function Return all physical pages marked as 
    present into a partition *)
Definition getMappedPagesOption (pd : page) (vaList : list vaddr) s : list (option page) :=
map (getMappedPage pd s) vaList.

(** The [getMappedPagesAux] function removes option type from mapped pages list *)
Definition getMappedPagesAux (pd :page)  (vaList : list vaddr) s : list page := 
filterOption (getMappedPagesOption pd vaList s).

(** The [readPDflag] function returns the flag value stored into a given table 
    at a given position in memory. The table should contain only virtual entries 
    (The type [VE] is already defined in [Model.ADT])  *)
Definition readPDflag  (paddr : page) (idx : index) memory : option bool:=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (VE a) => Some a.(pd)
  | Some _ => None
  | None => None
 end.

(**  The [getFstShadow] returns the physical page of the first shadow page of
     a given partition  *)
Definition getFstShadowInternal partition memory: option page:= 
match succIndexInternal sh1idx with 
|None => None
|Some idx => readPhysicalInternal partition idx memory
end. 

(** The [checkChild] function returns true if the given virtual address corresponds 
    to a child of the given partition 
    *)
Definition checkChild partition level (s:state) va : bool :=
let idxVA :=  getIndexOfAddr va fstLevel in 
match getFstShadowInternal partition s.(memory)  with 
| Some sh1  => 
   match getIndirection sh1 va level (nbLevel -1) s with 
    |Some tbl => if tbl =? defaultPage 
                    then false 
                    else match readPDflag tbl idxVA s.(memory) with 
                          |Some true => true
                          |_ => false
                          end
    |None => false 
    end
| _ => false
end.

(** The [getPdsVAddr] function returns the list of virtual addresses used as 
    partition descriptor into a given partition *)
Definition getPdsVAddr partition l1 (vaList : list vaddr) s :=
filter (checkChild partition l1 s) vaList.


(** The [getChildren] function Returns all children of a given partition *)
Definition getChildren (partition : page) s := 
let vaList := getAllVAddr in 
match getNbLevel, getPd partition s.(memory) with 
|Some l1,Some pd => getMappedPagesAux pd (getPdsVAddr partition l1 vaList s) s
|_, _ => []
end.

(** The [getPartitionsAux] function returns all pages marked as descriptor partition *)
Fixpoint getPartitionAux (partitionRoot : page) (s : W) bound {struct bound} : list page :=
  match bound with
    | O => []
    | S bound1 => partitionRoot :: flat_map (fun p => getPartitionAux p s bound1) 
                                    (getChildren partitionRoot s )
  end.

(** The [getPartitions] function fixes the sufficient timeout value to retrieve all partitions *)
Definition getPartitions (root : page) s : list page  :=
(getPartitionAux root s (nbPage+1)). 


(******* State properties *)

Definition isVA (p:page) (i:index) (s:W): Prop := match (lookup p i (s.(memory)) beqPage beqIndex) with 
             |Some (VA _) => True
             |_ => False
             end.

Definition nextEntryIsPP (p:page) (idx:index) (p':Value) (s:W) : Prop:= 
match succIndexInternal idx with 
| Some i => match lookup p i (memory s) beqPage beqIndex with 
                  | Some (PP table) => p' = cst value (PP table)
                  |_ => False 
                  end
| _ => False 
end.

Definition partitionDescriptorEntry (s:W) := 
forall (p : page),  
  In p (getPartitions multiplexer s)-> forall (idx : index), 
    (idx = PDidx \/ idx = sh1idx \/ idx = sh2idx \/ idx = sh3idx \/ idx = PPRidx  \/ idx = PRidx ) ->
    idx < tableSize - 1  /\ isVA p idx  s /\ exists (p1:page) , nextEntryIsPP p idx (cst value (PP p1)) s  /\  
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
unfold getSh1idx in X2.
inversion X2;subst.
auto.
inversion X3.
Qed.

(** about Succ *)

Require Import Coq.Logic.Eqdep.

Lemma succW  (x : Id) (P: Value -> W -> Prop) (v:Value) (fenv: funEnv) (env: valEnv) :
forall (idx:index), {{fun s => idx < (tableSize -1) /\ forall  l : idx + 1 < tableSize , 
    P (cst (option index) (succIndexInternal idx)) s /\ v = cst index idx }}  fenv >> (x,v)::env >> Succ x {{ P }}.
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
unfold b_exec in *.
unfold b_eval in *.
unfold xf_succ in *.
unfold b_mod in *.
simpl in *.
inversion X4;subst.
apply H1.
inversion X5.
inversion X5.
contradiction.
Qed.

Lemma succWp (x:Id) (v:Value) P (fenv: funEnv) (env: valEnv) :
forall (idx:index), {{fun s => P s  /\ idx < tableSize - 1 /\ v=cst index idx}} fenv >> (x,v)::env >> Succ x 
{{fun (idxsuc : Value) (s : state) => P s  /\ cst (option index) (succIndexInternal idx) = idxsuc }}.
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
split. 
intuition.
intuition.
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
intros; simpl.
eapply BindS_VHTT1.
eapply weakenEval.
eapply succW.
Admitted.


End Hoare_Test_FstShadow.
