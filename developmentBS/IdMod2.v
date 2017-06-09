Require Import EnvListAux7.
Require Import IdModType. 
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.ProofIrrelevance.

(*
Parameter CId : Type.

Parameter CIdEqDec : forall (x y : CId), {x = y} + {x <> y}.

Instance CIdEq: DEq CId :=
{
  dEq := CIdEqDec
}.
*)

Lemma valTyp_irrelevance : forall (T: Type) (p1 p2: ValTyp T), p1 = p2.
intros.
eapply proof_irrelevance.  
Qed.


Instance pstate_nat : PState nat := {|

   loc_pi := valTyp_irrelevance;

   b_init := 0
|}.


(*
Parameter W2 : Type.

Parameter Loc_PI2 : forall (T: Type) (p1 p2: ValTyp T), p1 = p2.

Parameter BInit2 : W2.
*)

Module IdModM2 <: IdModType.

  Definition Id := string.

  Definition IdEqDec := string_dec.

  Instance IdEq2 : DEq Id :=
  {
  dEq := IdEqDec
  }.

  Definition IdEq := IdEq2.
  
  Definition W := nat.

  Definition Loc_PI := valTyp_irrelevance.

  Definition BInit := 0.

  Instance WP2 : PState W :=
  {
  loc_pi := Loc_PI;
  
  b_init := BInit
  }.              

  Definition WP := WP2.
  
End IdModM2.

