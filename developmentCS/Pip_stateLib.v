Require Import Pip_state Lib.

Require Import ProofIrrelevance  Coq.Program.Equality Arith List Omega.
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
let (i,_):=idx in 
  if lt_dec i tableSize 
  then Some (CIndex (i+1)) 
  else None.

Definition writeVirtualInternal (p:page) (i:index) (v:vaddr) :=
fun s => {| currentPartition := s.(currentPartition);
  memory :=   add p i (VA v)  s.(memory) beqPage beqIndex|}.

Module Index.
Definition geb (a b : index) : bool := b <=? a.
Definition leb (a b : index) : bool := a <=? b.
Definition ltb (a b : index) : bool := a <? b.
Definition gtb (a b : index) : bool := b <? a.
Definition eqb (a b : index) : bool := a =? b.
End Index. 

Module Page. 
Definition eqb (p1 : page)  (p2 : page) : bool := (p1 =? p2).
End Page.

Module Level. 
Definition gtb (a b : level) : bool := b <? a .
Definition eqb (a b : level) : bool:= a =? b.
Program Definition pred (n : level) : option level := 
if gt_dec n 0 then
let ipred := n-1 in 
Some (Build_level ipred _ )
else  None.
Next Obligation.
destruct n.
simpl.
omega.
Qed.
End Level. 

Module VAddr.
Definition eqbList(vaddr1 : vaddr) (vaddr2 : vaddr) : bool :=
 beqVAddr vaddr1 vaddr2.
End VAddr.

(** For conditions *)


(** The [getCurPartition] function returns the current partition descriptor of a given state *)
Definition getCurPartition s :page:=
currentPartition s. 

(** The [getMaxIndex] function returns the last position into a page table *) 
Definition getMaxIndex : option index:=
match gt_dec tableSize 0 with
| left x =>
    Some (CIndex (tableSize-1))
| right _ => None 
end. 

(** The [readPhysical] function returns the physical page stored into a given 
    page at a given position in physical memory. The table should contain only Physical pages 
    (The type [PP] is already defined into [Model.ADT]) *)
Definition readPhysical (paddr : page) (idx : index) memory: option page :=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (PP a) => Some a
  | _ => None
 end.

(**  The [getPd] function returns the physical page of the page directory of
     a given partition  *)
Definition getPd partition memory: option page:= 
match succIndexInternal PDidx with 
|None => None
|Some idx => readPhysical partition idx memory
end. 

(**  The [getFstShadow] returns the physical page of the first shadow page of
     a given partition  *)
Definition getFstShadow partition memory: option page:= 
match succIndexInternal sh1idx with 
|None => None
|Some idx => readPhysical partition idx memory
end. 

(**  The [getSndShadow] returns the physical page of the second shadow page  of
     a given partition *)
Definition getSndShadow partition memory: option page:= 
match succIndexInternal sh2idx with 
|None => None
|Some idx => readPhysical partition idx memory
end. 

(**  The [getConfigTablesLinkedList] returns the physical address of the indirection tables
 reverse translation of a given partition  *)
Definition getConfigTablesLinkedList partition memory: option page:= 
match succIndexInternal sh3idx with 
|None => None
|Some idx => readPhysical partition idx memory
end. 

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

(** The [getNbLevel] function returns the number of translation levels of the MMU *) 
Definition getNbLevel : option level:=
if gt_dec nbLevel 0
then Some (CLevel (nbLevel-1))
else None.

(** The [readPresent] function returns the flag value stored into a given table 
    at a given position in memory. The table should contain only Physical entries *)
Definition readPresent  (paddr : page) (idx : index) memory : option bool:=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (PE a) => Some a.(present)
  | Some _ => None
  | None => None
 end. 

(** The [readAccessible] function returns the flag value stored into a given table 
    at a given position in memory. The table should contain only Physical entries  *)
Definition readAccessible  (paddr : page) (idx : index) memory : option bool:=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (PE a) => Some a.(user)
  | Some _ => None
  | None => None
 end. 

Definition getIndexOfAddr (va : vaddr) (l : level) : index:=
nth ((length va) - (l + 2))  va defaultIndex .

(** The [checkVAddrsEqualityWOOffset] function compares two given virtual addresses 
    without taking into account the last index *)
Fixpoint checkVAddrsEqualityWOOffset (timeout : nat) (va1 va2 : vaddr) (l : level) := 
match timeout with 
|0 => true
|S timeout1 =>  
let idx1 := getIndexOfAddr va1 l in
 let idx2 := getIndexOfAddr va2 l in
if Level.eqb l fstLevel 
then
      (idx1 =? idx2) 
    else 
      match Level.pred l with 
      | Some levelpred =>  if idx1 =? idx2 
                              then checkVAddrsEqualityWOOffset timeout1 va1 va2 levelpred
                              else false
      | _ => true
      end
end. 

(** The [readPhyEntry] function returns the physical page stored into a given table 
    at a given position in memory. The table should contain only Physical entries *)
Definition readPhyEntry(paddr : page) (idx : index) memory: option page :=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (PE a) => Some a.(pa)
  | Some _ => None
  | None => None
 end. 

(** The [readIndex] function returns the index stored into a given table 
    at a given position in memory. The table should contain only indices  *)
Definition readIndex  (paddr : page) (idx : index) memory : option index :=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (I indexValue) => Some indexValue
  | Some _ => None
  | None => None
 end. 
 
 (** The [readVirtual] function returns the virtual address strored into a given table 
    at a given position in memory. The table should contain a virtual address at this position *)
Definition readVirtual (paddr : page) (idx : index) memory : option vaddr :=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (VA addr) => Some addr
  | Some _ => None
  | None => None
 end. 

(** The [readVirEntry] function returns the virtual address strored into a given table 
    at a given position in memory. The table should contain a VEntry at this position *)
Definition readVirEntry (paddr : page) (idx : index) memory : option vaddr :=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (VE addr) => Some (vad addr)
  | Some _ => None
  | None => None
 end. 
 
(** The [getDefaultPage] function returns the value of the default page *)
Definition getDefaultPage := defaultPage.

(** The [getIndirection] function returns the configuration table entry that corresponds 
    to the given level and virtual address *)
Fixpoint  getIndirection (pd : page) (va : vaddr) (currentlevel : level) (stop : nat) s :=
match stop with 
|0 => Some pd 
|S stop1 => 
if (Level.eqb currentlevel fstLevel)  
then Some pd 
  else  
    let idx :=  getIndexOfAddr va currentlevel in 
       match readPhyEntry pd idx s.(memory) with 
       | Some addr =>  if  defaultPage =? addr 
                          then Some defaultPage 
                          else 
                            match Level.pred currentlevel with
                            |Some p =>  getIndirection addr va p stop1 s
                            |None => None
                            end
      |None => None
    end
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

(** The [getVirtualAddressSh2] function returns the virtual address stored into the 
    second shadow structure which corresponds to a given virtual address **)
Definition getVirtualAddressSh2 sh2 s va: option vaddr :=
match getNbLevel  with 
 |None => None
 |Some level => let idxVA := getIndexOfAddr va fstLevel  in 
               match getIndirection sh2 va level (nbLevel - 1) s with 
                | Some tbl =>  if defaultPage =? tbl
                                   then None 
                                   else readVirtual tbl idxVA s.(memory) 
                | _ => None
               end
end.

(** The [getVirtualAddressSh2] function returns the virtual address stored into the 
    parent **)
Definition getVAInParent partition s va: option vaddr :=
match getSndShadow partition (memory s) with 
|Some sh2 => match getVirtualAddressSh2 sh2 s va with 
             | Some vainparent =>  if (VAddr.eqbList defaultVAddr vainparent) 
                                     then None 
                                     else Some vainparent
             | _ => None
             end
| _ => None
end. 

(** The [getVirtualAddressSh1] function returns the virtual address stored into the first
   shadow structure which corresponds to a given virtual address **)
Definition getVirtualAddressSh1 sh1 s va: option vaddr :=
match getNbLevel  with 
 |None => None
 |Some level => let idxVA := getIndexOfAddr va fstLevel  in 
               match getIndirection sh1 va level (nbLevel - 1) s with 
                | Some tbl =>  if defaultPage =? tbl
                                   then None 
                                   else readVirEntry tbl idxVA s.(memory) 
                | _ => None
               end
end.

(** The [getAccessibleMappedPage] function returns the physical page stored into a leaf node, 
   which corresponds to a given virtual address, if the present and user flags are equal to true **)
Definition getAccessibleMappedPage pd s va: option page :=
match getNbLevel  with 
 |None => None
 |Some level =>let idxVA := getIndexOfAddr va fstLevel  in 
               match getIndirection pd va level (nbLevel - 1) s with 
                | Some tbl => if defaultPage =? tbl
                                   then None 
                                   else  match (readPresent tbl idxVA s.(memory)),
                                                   (readAccessible tbl idxVA s.(memory)) with 
                                           |Some true, Some true => readPhyEntry tbl idxVA s.(memory) 
                                           | _, _ =>  None 
                                          end
                | _ => None
               end
end.

(** The [geTrdShadows] returns physical pages used to keep informations about 
    configuration pages 
*)
Fixpoint getTrdShadows (sh3 : page) s bound :=
match bound with 
|0 => []
|S bound1 => match getMaxIndex with 
            |None => []
            |Some maxindex =>  match readPhysical sh3 maxindex s.(memory) with 
                                |None => [sh3]
                                |Some addr => if addr =? defaultPage then [sh3] else sh3 :: getTrdShadows addr s bound1
                               end
           end
end.

(** The [checkChild] function returns true if the given virtual address corresponds 
    to a child of the given partition 
    *)
Definition checkChild partition level (s:state) va : bool :=
let idxVA :=  getIndexOfAddr va fstLevel in 
match getFstShadow partition s.(memory)  with 
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

(** The [getTablePages] function returns the list of physical pages stored into 
    a given configuration table from a given index *)
Fixpoint getTablePages (table : page ) (idx : nat) s : list page := 
match idx with 
| 0 => []
|S idx1 => match  lookup table (CIndex idx1) s.(memory) beqPage beqIndex  with 
              | Some (PE entry) => if (pa entry =? defaultPage ) then getTablePages table idx1 s
                                      else getTablePages table idx1 s ++ [pa entry] 
              | _ => getTablePages table idx1 s
            end
end.

Fixpoint getIndirectionsAux (pa : page) (s : state) level {struct level} : list page :=
  match level with
    | O => []
    | S level1 => pa :: flat_map (fun p => getIndirectionsAux p s level1) 
                                    (getTablePages pa tableSize s)
  end.

(** The [getIndirectionsAux] function returns the list of physical pages 
    used into a configuration tables tree *)
Definition getIndirections pd s : list page :=
  getIndirectionsAux pd s nbLevel.

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
  
(** The [getPdsVAddr] function returns the list of virtual addresses used as 
    partition descriptor into a given partition *)
Definition getPdsVAddr partition l1 (vaList : list vaddr) s :=
filter (checkChild partition l1 s) vaList.

(** The [getMappedPagesOption] function Return all physical pages marked as 
    present into a partition *)
Definition getMappedPagesOption (pd : page) (vaList : list vaddr) s : list (option page) :=
map (getMappedPage pd s) vaList.

(** The [getAccessibleMappedPagesOption] function Return all physical pages 
    marked as present and accessible into a partition *)
Definition getAccessibleMappedPagesOption (pd : page) (vaList : list vaddr) s : list (option page) :=
map (getAccessibleMappedPage pd s) vaList.

(** The [filterOption] function Remove option type from list *)
Fixpoint filterOption (l : list (option page)) := 
match l with 
| [] => []
| Some a :: l1 => a:: filterOption l1
|None :: l1 => filterOption l1
end.

(** The [getMappedPagesAux] function removes option type from mapped pages list *)
Definition getMappedPagesAux (pd :page)  (vaList : list vaddr) s : list page := 
filterOption (getMappedPagesOption pd vaList s).

(** The [getAccessibleMappedPagesAux] function removes option type from 
    accessible mapped pages list *)
Definition getAccessibleMappedPagesAux (pd :page)  (vaList : list vaddr) s : list page := 
filterOption (getAccessibleMappedPagesOption pd vaList s).

(** The [getConfigPagesAux] function returns all configuration pages of a 
    given partition *)
Definition getConfigPagesAux (partition : page) (s : state) : list page := 
let vaList := getAllVAddr in 
match getPd partition s.(memory), 
      getFstShadow partition s.(memory), 
      getSndShadow partition s.(memory), 
      getConfigTablesLinkedList partition s.(memory)  with 
| Some pd , Some sh1, Some sh2 , Some sh3  => (getIndirections pd s)++
                         (getIndirections sh1 s)++
                         (getIndirections sh2 s )++
                         (getTrdShadows sh3 s (nbPage+1))
|_,_,_,_ => []
end.

Definition getConfigPages (partition : page) (s : state) :=
partition :: (getConfigPagesAux partition s). 

(** The [getMappedPages] function Returns all present pages of a given partition *)
Definition getMappedPages (partition : page) s : list page :=
  match getPd partition s.(memory) with
    |None => []
    |Some pd => let vaList := getAllVAddr in getMappedPagesAux pd vaList s
  end.

(** The [getAccessibleMappedPages] function Returns all present and 
    accessible pages of a given partition *)
Definition getAccessibleMappedPages (partition : page) s : list page :=
  match getPd partition s.(memory) with
    |None => []
    |Some pd => let vaList := getAllVAddr in getAccessibleMappedPagesAux pd vaList s
  end.
  
(** The [getUsedPages] function Returns all used pages (present and config pages)
    of a given partition including the partition descriptor itself *)
Definition getUsedPages (partition: page) s : list page :=
  getConfigPages partition s ++ getMappedPages partition s.

Lemma  eqPageDec : forall n m : page, {n = m} + {n <> m}.
Proof.
intros.
destruct n. destruct m.
assert ({p = p0} + {p <> p0}).
apply eq_nat_dec.
destruct H.
left.
subst.
assert(Hp = Hp0) by apply proof_irrelevance.
subst.
trivial.
right.
unfold not in *.
intros. apply n.
clear n.
inversion H. trivial.
Qed.

(** The [getChildren] function Returns all children of a given partition *)
Definition getChildren (partition : page) s := 
let vaList := getAllVAddr in 
match getNbLevel, getPd partition s.(memory) with 
|Some l1,Some pd => getMappedPagesAux pd (getPdsVAddr partition l1 vaList s) s
|_, _ => []
end.


(** The [getPartitionsAux] function returns all pages marked as descriptor partition *)
Fixpoint getPartitionAux (partitionRoot : page) (s : state) bound {struct bound} : list page :=
  match bound with
    | O => []
    | S bound1 => partitionRoot :: flat_map (fun p => getPartitionAux p s bound1) 
                                    (getChildren partitionRoot s )
  end.

(** The [getPartitions] function fixes the sufficient timeout value to retrieve all partitions *)
Definition getPartitions (root : page) s : list page  :=
(getPartitionAux root s (nbPage+1)). 

(** The [getParent] function returns the parent partition descriptor of a given partition *)
Definition getParent partition memory :=
match succIndexInternal PPRidx with 
| Some idx =>  readPhysical partition idx memory
| _ => None 
end.

(** The [getAncestorsAux] function returns the ancestors list of a given partition *)
Fixpoint getAncestorsAux (partition : page) memory depth : list page := 
match depth with 
|0 => [] 
| S depth1 => match getParent partition memory with 
               | Some parent => parent :: getAncestorsAux parent memory depth1
               | _ => []
              end
end.

(** The [getAncestors] function fixes the sufficient timeout value to retrieve all ancestors *)
Definition getAncestors (partition : page) s := 
getAncestorsAux partition s.(memory) (nbPage+1). 

(** Propositions *)
(** The [isPE] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [PE] *)
Definition isPE table idx s: Prop := 
match lookup table idx s.(memory) beqPage beqIndex with 
             |Some (PE _) => True
             |_ => False
end. 

(** The [isVE] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [VE] *)
Definition isVE table idx s: Prop := 
 match lookup table idx s.(memory) beqPage beqIndex with 
             |Some (VE _) => True
             |_ => False
end.

(** The [isVA] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [VA] *)
Definition isVA table idx s: Prop := 
 match lookup table idx s.(memory) beqPage beqIndex with 
             |Some (VA _) => True
             |_ => False
end.

(** The [isPP] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [PE] *)
Definition isPP table idx s: Prop := 
 match lookup table idx s.(memory) beqPage beqIndex with 
             |Some (PP _) => True
             |_ => False
end.

(** The [isPP'] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [PP] and physical page stored into this entry 
    is equal to a given physical page [pg]*)
Definition isPP' table idx pg s: Prop := 
 match lookup table idx s.(memory) beqPage beqIndex with 
             |Some (PP p) => p = pg
             |_ => False
end.

(** The [nextEntryIsPP] proposition reutrns True if the entry at position [idx+1]
    into the given physical page [table] is type of [PP] and physical page stored into 
    this entry is equal to a given physical page [pg] *)
Definition nextEntryIsPP table idxroot tableroot s : Prop:= 
match succIndexInternal idxroot with 
| Some idxsucc => match lookup table idxsucc (memory s) beqPage beqIndex with 
                  | Some (PP table) => tableroot = table
                  |_ => False 
                  end
| _ => False 
end.

(** The [entryPresentFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [PP] and the present flag stored into 
    this entry is equal to a given flag [flag] *)
Definition entryPresentFlag table idx flag s:= 
match lookup table idx s.(memory) beqPage beqIndex with 
| Some (PE entry) => flag =  entry.(present)
| _ => False
end. 

(** The [entryPDFlag]  proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the pd flag stored into 
    this entry is equal to a given flag [flag] *)
Definition entryPDFlag table idx flag s:= 
match lookup table idx s.(memory) beqPage beqIndex with 
| Some (VE entry) => flag =  entry.(pd)
| _ => False
end. 

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into 
    this entry is equal to a given flag [flag] *)
Definition entryUserFlag table idx flag s:= 
match lookup table idx s.(memory) beqPage beqIndex with 
| Some (PE entry) => flag =  entry.(user)
| _ => False
end. 

(** The [VEDerivation] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the given boolean value 
    [res] specifies if the virtual address stored into  
    this entry is equal or not to the default virtual address *)
Definition VEDerivation table idx (res : bool) s:= 
match lookup table idx s.(memory) beqPage beqIndex with 
| Some (VE entry) => ~ (beqVAddr entry.(vad) defaultVAddr) = res
| _ => False
end. 

(** The [isEntryVA] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the virtual address
    stored into this entry is equal to a given virtual address [v1] *)
Definition isEntryVA table idx v1 s:=
 match lookup table idx (memory s) beqPage beqIndex with 
 | Some (VE entry)  => entry.(vad) = v1
 | _ => False
 end.

(** The [isVA'] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VA] and the virtual address
    stored into this entry is equal to a given virtual address [v1] *)
Definition isVA' table idx v1 s:=
 match lookup table idx (memory s) beqPage beqIndex with 
 | Some (VA entry)  => entry = v1
 | _ => False
 end.

(** The [isEntryPage] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [PE] and physical page stored into this entry 
    is equal to a given physical page [page1]*)
Definition isEntryPage table idx page1 s:=
 match lookup table idx (memory s) beqPage beqIndex with 
 | Some (PE entry)  => entry.(pa) = page1
 | _ => False
 end.
 
(** The [getTableAddrRoot'] proposition returns True if the given physical page [table]
is a configuration table into different structures (pd, shadow1 or shadow2). This table should be associated to the 
given virtual address [va]  *)
Definition getTableAddrRoot' (table : page) (idxroot : index) 
(currentPart : page) (va : vaddr) (s : state) : Prop :=
(idxroot = PDidx \/ idxroot = sh1idx \/ idxroot = sh2idx) /\
(forall tableroot : page,
 nextEntryIsPP currentPart idxroot tableroot s ->
 exists nbL : level,
   Some nbL = getNbLevel /\
   (exists stop : nat, stop > 0 /\ stop <= nbL /\ getIndirection tableroot va nbL stop s = Some table)).

(** The [getTableAddrRoot] proposition returns True if the given physical page [table]
is the last page table into a structure (pd, shadow1 or shadow2) that corresponds to a given virtual address [va] *)
Definition getTableAddrRoot table idxroot currentPart va s : Prop :=
(idxroot = PDidx \/ idxroot = sh1idx \/ idxroot = sh2idx)/\
   forall (tableroot : page), nextEntryIsPP  currentPart idxroot tableroot s ->  
   exists nbL, Some nbL = getNbLevel  /\ exists (stop :nat) , stop = nbL+1  /\ 
    getIndirection tableroot va nbL stop s = Some table . 

(** The [getAllPages] returns the list of all physical pages *)
Definition getAllPages: list page:= 
map CPage (seq 0 nbPage ).

(** The [getPDFlag] checks if the given virtual address corresponds to a partition
    descriptor **)
Definition getPDFlag sh1 va s :=
let idxVA := getIndexOfAddr va fstLevel in
match getNbLevel with
|Some nbL =>  match getIndirection sh1 va nbL (nbLevel - 1) s with
  | Some tbl =>
      if tbl =? defaultPage
      then false
      else
       match readPDflag tbl idxVA (memory s) with
       | Some true => true
       | Some false => false
       | None => false
       end
  | None => false
  end
| None => false
end.

(** The [isAccessibleMappedPageInParent] function returns true if the given physical
    page is accessible in the parent of the given partition **)
Definition isAccessibleMappedPageInParent partition va accessiblePage s  :=
match getSndShadow partition (memory s) with 
| Some sh2 => 
  match  getVirtualAddressSh2 sh2 s va  with 
   | Some vaInParent => 
     match getParent partition (memory s) with 
      | Some parent => 
        match getPd parent (memory s) with 
         | Some pdParent => 
           match getAccessibleMappedPage pdParent s vaInParent with 
            | Some sameAccessiblePage => accessiblePage =? sameAccessiblePage
            | None => false
           end
         | None => false
        end
    | None => false
           end
| None => false
           end
| None => false
end.

(** The [isPartitionFalse] returns true if the partition descriptor flag of a given
     entry is equal to false or there is no data stored into this entry **)  
Definition isPartitionFalse ptPDChildSh1 idxPDChild s :=
readPDflag ptPDChildSh1 idxPDChild (memory s) = Some false \/
readPDflag ptPDChildSh1 idxPDChild (memory s) = None.

(** The [isAncestor] funtion returns true if the given partitions are equal 
    or the descParent partition is an ancestor of currentPart **)
Definition isAncestor  currentPart descParent s :=
( currentPart = descParent \/ In descParent (getAncestors currentPart s)).

Definition isWellFormedFstShadow nbL table  s:= 
(nbL <> fstLevel /\ 
(forall idx, readPhyEntry table  idx s.(memory) = Some defaultPage /\ 
readPresent table idx (memory s) = Some false )) \/ 
(nbL = fstLevel /\ 
( forall idx : index, 
(readVirEntry table idx (memory s) = Some defaultVAddr) /\ 
readPDflag table idx (memory s) = Some false) ).

Definition isWellFormedSndShadow nbL table  s:= 
(nbL <> fstLevel /\ (
forall idx, readPhyEntry table  idx s.(memory) = Some defaultPage /\ 
readPresent table idx (memory s) = Some false )) \/ 
(nbL = fstLevel /\ ( forall idx : index, 
(readVirtual table idx (memory s) = Some defaultVAddr) ) ).

(** The [isDerived] funtion returns true if a physical page is derived 
    into the given partition , this physical page is associated to the given 
    virtual address [va] **)
Definition isDerived partition va  s  :=
match getFstShadow partition (memory s) with 
| Some sh1 => 
  match  getVirtualAddressSh1 sh1 s va  with 
   | Some va0 => beqVAddr defaultVAddr va0 = false
   | _ => False
  end
| None => False
end.

Lemma  pageDec :
forall x y : page, {x = y} + {x <> y}.
Proof.
intros.
destruct x; destruct y.
assert({p = p0} + {p <> p0}).
apply Nat.eq_dec.
destruct H.
left.
subst.
f_equal.
apply proof_irrelevance.
right.
contradict n.
inversion n.
subst;trivial.
Qed.

Fixpoint closestAncestorAux part1 part2 s bound : option page :=
match bound  with
| 0 => None
| S bound1 => match getParent part1 (memory s) with
              | Some parent => match in_dec pageDec part2 
                                    (getPartitionAux parent s (nbPage+1)) with 
                               | left _  => Some parent
                               | _ =>  closestAncestorAux parent part2 s bound1
                               end 
              | None =>  Some multiplexer 
              end 
end.

Definition closestAncestor part1 part2 s := 
closestAncestorAux part1 part2 s (nbPage+1).


Ltac symmetrynot :=
match goal with
| [ |- ?x <> ?y ] => unfold not ; let Hk := fresh in intro Hk ; symmetry in Hk ;contradict Hk
end.





