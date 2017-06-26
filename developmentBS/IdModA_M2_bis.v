Require Import EnvListAux7.
Require Import IdModType. 
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.ProofIrrelevance.


Lemma valTyp_irrelevance : forall (T: Type) (p1 p2: ValTyp T), p1 = p2.
intros.
eapply proof_irrelevance. 
Qed.

Module IdModA_M2_b <: IdModType.
 
  Definition Id := string.

  Definition IdEqDec := string_dec.

  Instance IdEq2 : DEq Id :=
  {
  dEq := IdEqDec
  }.

  Inductive page :Type := P (v:nat).
  Inductive index :Type := I (v:nat).
  Definition vAddress :Type := list index.
  Inductive vEntry :Type := VE (a:vAddress).
  Inductive pEntry :Type := PE (p:page).
  Inductive sValue : Type := SP:page->sValue 
                            |SI:index->sValue
                            |SVA:vAddress->sValue
                            |SVE:vEntry->sValue
                            |SPE:pEntry->sValue.

  Definition Vpage (p:page) :nat := match p with |P p' => p' end.
  Definition Vindex (i:index) :nat := match i with |I i' => i' end.
  Fixpoint VvAddress (a:vAddress) :(list nat) := 
        match a with 
          | nil => nil
          |cons (I i) ls => cons i (VvAddress ls)
        end.
  Definition VvEntry (a:vEntry) :list nat := match a with 
                    |VE a' => VvAddress a' end.
  Definition VpEntry (a:pEntry) :nat := match a with | PE a' => Vpage a' end.
  
  Definition paddr := prod page index.

  Definition IdEq := IdEq2.

  Record state : Type := {
   currentPartition : page;
   memory : list (paddr * sValue);
   partitions : list page
  }.
  
  Definition W := state.

  Definition Loc_PI := valTyp_irrelevance.

  Definition page0:page := P 0.

  Definition BInit := {|
          currentPartition := page0 ;
          memory:= @nil (paddr * sValue);
          partitions := @nil page
                      |}.

  Instance WP2 : PState W :=
  {
  loc_pi := Loc_PI;
 
  b_init := BInit
  }.             

  Definition WP := WP2.

End IdModA_M2_b.

