Require Import EnvListAux7.
Require Import IdModType. 
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.ProofIrrelevance.
Require Import ADT.
Require Import Hardware.


Lemma valTyp_irrelevance : forall (T: Type) (p1 p2: ValTyp T), p1 = p2.
intros.
eapply proof_irrelevance. 
Qed.


Module IdModA_M2 <: IdModType.
 
  Definition Id := string.

  Definition IdEqDec := string_dec.

  Instance IdEq2 : DEq Id :=
  {
  dEq := IdEqDec
  }.

  Definition IdEq := IdEq2.
 
  Definition W := state.

  Definition Loc_PI := valTyp_irrelevance.

  Lemma Hpx : 0 < nbPage.
  Proof.
  specialize nbPageNotZero as H.
  inversion H.
  auto.
  auto.
  Qed.
  

  Definition BInit := {|
          currentPartition := {| p:=0 ; Hp := Hpx |} ;
          memory:= @nil (paddr * value)
                      |}.

  Instance WP2 : PState W :=
  {
  loc_pi := Loc_PI;
 
  b_init := BInit
  }.             

  Definition WP := WP2.

End IdModA_M2.

