Require Import EnvListAux7.
Require Import IdModType. 
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.ProofIrrelevance.


Lemma valTyp_irrelevance : forall (T: Type) (p1 p2: ValTyp T), p1 = p2.
intros.
eapply proof_irrelevance. 
Qed.


Module IdMod <: IdModType.
 
  Definition Id := string.

  Definition IdEqDec := string_dec.

  Instance IdEq2 : DEq Id :=
  {
  dEq := IdEqDec
  }.

  Definition IdEq := IdEq2.
 
  Definition W := list (Id * nat).

  Definition Loc_PI := valTyp_irrelevance.

  Definition BInit := @nil (Id * nat).

  Instance WP2 : PState W :=
  {
  loc_pi := Loc_PI;
 
  b_init := BInit
  }.             

  Definition WP := WP2.

End IdMod.

