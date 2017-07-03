Require Import Pip_state Lib.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Import List.ListNotations.

(** Internals *)

Definition readPhysicalInternal p i memory :option page := 
match (lookup p i memory beqPage beqIndex) with
                            | Some (PP a) => Some a
                            | _ => None
                       end.

Definition readVirtualInternal p i memory : option vaddr:=
  match (lookup p i memory beqPage beqIndex) with
  | Some (VA a) => Some a
  | _ => None
  end.

Definition succIndexInternal (idx:index) : option index :=
let (i,P):=idx in 
  if lt_dec i tableSize 
  then Some (CIndex (i+1)) 
  else None.

Definition writeVirtualInternal (p:page) (i:index) (v:vaddr) :=
fun s => {| currentPartition := s.(currentPartition);
  memory :=   add p i (VA v)  s.(memory) beqPage beqIndex|}.

(** For conditions *)

(** The [getAllIndicesAux] function returns the list of all indices  *)
Fixpoint getAllIndicesAux (pos count: nat) : list index :=
  match count with
    | 0        => []
    | S count1 => match lt_dec pos tableSize with
                   | left pf => Build_index pos pf :: getAllIndicesAux (S pos) count1
                   | _       => []
                 end
  end.

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
Fixpoint getPartitionAux (partitionRoot : page) s bound {struct bound} : list page :=
  match bound with
    | O => []
    | S bound1 => partitionRoot :: flat_map (fun p => getPartitionAux p s bound1) 
                                    (getChildren partitionRoot s )
  end.

(** The [getPartitions] function fixes the sufficient timeout value to retrieve all partitions *)
Definition getPartitions (root : page) s : list page  :=
(getPartitionAux root s (nbPage+1)). 


