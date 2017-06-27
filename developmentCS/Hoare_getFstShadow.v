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

Definition xf_read (p: page) : XFun index (option value) := {|
   b_mod := fun s i => match (lookup p i s.(memory) beqPage beqIndex) with
                            | Some (PP a) => (s,Some (PP a))
                            | _ => (s,None) 
                       end  
|}.                                  

Instance VT_index : ValTyp index.
Instance VT_option_value : ValTyp (option value).

Definition ReadPhysical (p:page) (x:Id) : Exp :=
  Modify index (option value) VT_index VT_option_value (xf_read p) (Var x).  

(** Succ -index : calculates the successor of an index *)                 

Definition succInternal (idx:index) : option index :=
let (i,P):=idx in 
  if lt_dec i tableSize 
  then Some (CIndex i) 
  else None.

Definition xf_succ : XFun index (option index) := {|
   b_mod := fun s (idx:index) =>  (s, succInternal idx)
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

(******* State properties *)

(** partitionDescriptorEntry *) 
Definition isVA (p:page) (i:index) (s:W): Prop := match (lookup p i (s.(memory)) beqPage beqIndex) with 
             |Some (VA _) => True
             |_ => False
             end.

Definition nextEntryIsPP (p:page) (idx:index) (p':Value) (s:W) : Prop:= 
match succInternal idx with 
| Some i => match lookup p i (memory s) beqPage beqIndex with 
                  | Some (PP table) => p' = cst value (PP table)
                  |_ => False 
                  end
| _ => False 
end.

Definition getPartitions (multiplexer:page) (s:W) := @nil page.

Definition partitionDescriptorEntry (s:W) := 
forall (p : page),  
In p (getPartitions multiplexer s)-> 
forall (idx : index), (idx = PDidx \/ idx = sh1idx \/ idx = sh2idx \/ idx = sh3idx \/ idx = PPRidx  \/ idx = PRidx ) ->
isVA p idx  s /\ 
exists (p1:page) , nextEntryIsPP p idx (cst value (PP p1)) s  /\  
(cst page p1) <> (cst page pageinit).

(** Hoare Triple *)

Lemma getFstShadow1 (partition : page) (P : W -> Prop) (fenv: funEnv) (env: valEnv) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ In partition (getPartitions multiplexer s)}}
fenv >> env >> (getFstShadow partition) 
{{fun (sh1 : Value) (s : state) => P s /\ nextEntryIsPP partition sh1idx sh1 s}}.
Admitted.


End Hoare_Test_FstShadow.
