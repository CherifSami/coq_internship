

Require Export Basics.
Require Export Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.

Require Import Coq.Logic.ProofIrrelevance.
Require Export Coq.Structures.Equalities.

Require Export EnvListAux7. 


(** general environment type - partial maps *)

Inductive findET {K V: Type} {h: DEq K} (m: Envr K V) (k: K) : V -> Type :=
  FindET : forall x: V, findE m k = Some x -> findET m k x.

Inductive findET2 {K V: Type} {h: DEq K} (m: Envr K V) (k: K) : V -> Type :=
  FindET2 : forall (v: V) (m0 m1: Envr K V),
            m = overrideE m0 (updateE m1 k v) ->  
            findE m0 k = None ->  
            findET2 m k v.

(************************************************************************)


Inductive MatchEnvsT {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type) : 
          Envr K V1 -> Envr K V2 -> Type :=
| MatchEnvs_NilT : MatchEnvsT rel nil nil
| MatchEnvs_ConsT : forall ls1 ls2 k v1 v2,
                     rel v1 v2 ->
                     MatchEnvsT rel ls1 ls2 ->
                     MatchEnvsT rel ((k,v1)::ls1) ((k,v2)::ls2).


Inductive MatchEnvs2BT {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type)  
          (k: K) (v1: V1) (v2: V2) : Envr K V1 -> Envr K V2 -> Type :=
| MatchEnvs2B_splitT : forall ls5 ls6 ls1 ls2 ls3 ls4,
                     rel v1 v2 ->
                     MatchEnvsT rel ls1 ls2 ->
                     MatchEnvsT rel ls3 ls4 ->
                     findE ls2 k = None -> 
                     ls5 = ls1 ++ ((k,v1)::ls3) ->
                     ls6 = ls2 ++ ((k,v2)::ls4) ->
            MatchEnvs2BT rel k v1 v2 ls5 ls6.                         

(*
Definition VectorMapRel (V1 V2: Type) (R: V1 -> V2 -> Prop) (n: nat) 
   (a1: t V1 n) (a2: t V2 n) : Prop :=
   forall i: Fin.t n, R (nth a1 i) (nth a2 i). 
*)
(*********************************************************************)


Inductive Forall3AT {A B :Type} (R: A -> B -> Type)
          (P: forall (a:A) (b:B), R a b -> Type) :
           list A -> list B -> Type :=
| Forall3AT_nil : Forall3AT R P nil nil
| Forall3AT_cons : forall (aas: list A) (bbs: list B) 
                        (a:A) (b:B) (p: R a b),
                   P a b p ->
                   Forall3AT R P aas bbs ->                          
                   Forall3AT R P (a::aas) (b::bbs).              


Inductive Forall3T {K A B :Type} (R: A -> B -> Type)
                    (P: forall (a:A) (b:B), R a b -> Type) :
           Envr K A -> Envr K B -> Type :=
| Forall3T_nil : Forall3T R P nil nil
| Forall3T_cons : forall (aas: Envr K A) (bbs: Envr K B) 
                        (x:K) (a:A) (b:B) (p: R a b),
                   P a b p ->
                   Forall3T R P aas bbs ->                          
                   Forall3T R P ((x,a)::aas) ((x,b)::bbs).              


Inductive Forall2BT {K A B :Type} {h: DEq K} (R: A -> B -> Type)
          (P: forall (a:A) (b:B), R a b -> Type)
          (Q: forall (ls1: Envr K A) (ls2: Envr K B),
                     MatchEnvsT R ls1 ls2 -> Type) :
          K -> A -> B -> Envr K A -> Envr K B -> Type :=
 Forall2BT_split : forall (aas as1 as2: Envr K A)
                         (bbs bs1 bs2: Envr K B) 
                         (k:K) (a:A) (b:B)
                         (p1: MatchEnvsT R as1 bs1)
                         (p2: MatchEnvsT R as2 bs2)
                         (p0: R a b),
                 aas = as1 ++ ((k,a)::as2) ->
                 bbs = bs1 ++ ((k,b)::bs2) ->
                 Q as1 bs1 p1 ->
                 Q as2 bs2 p2 ->
                 P a b p0 -> 
                 Forall2BT R P Q k a b aas bbs. 



(*********************************************************************)

Lemma consEnvLemmaT {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type)
              (env1: Envr K V1) (env2: Envr K V2) (x: K)
                      (v1: V1) (v2: V2):
    MatchEnvsT rel env1 env2 ->
    rel v1 v2 -> 
    MatchEnvsT rel ((x, v1)::env1) ((x, v2)::env2).  
Proof.
  intros.
  constructor.
  assumption.
  assumption.
Defined.


Lemma updateEnvLemmaT {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type)
              (env1: Envr K V1) (env2: Envr K V2) (x: K)
                      (v1: V1) (v2: V2):
    MatchEnvsT rel env1 env2 ->
    rel v1 v2 -> 
    MatchEnvsT rel (updateE env1 x v1) (updateE env2 x v2).  
Proof.
  unfold updateE.
  eapply consEnvLemmaT. 
Defined.
  

Lemma appEnvLemmaT {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type): 
     forall (env1A env1B: Envr K V1) (env2A env2B: Envr K V2), 
  MatchEnvsT rel env1A env2A ->
  MatchEnvsT rel env1B env2B -> 
  MatchEnvsT rel (env1A ++ env1B) (env2A ++ env2B).  
Proof.
  induction env1A.
  intros. 
  induction env2A.
  simpl.
  assumption.
  inversion X.  
  induction env2A.
  intros.
  inversion X.  
  intros.
  simpl.
  destruct a.
  destruct a0.
  destruct (dEq k k0).
  Focus 2.
  inversion X; subst.  
  intuition n.
  destruct e.
  inversion X; subst.
  constructor.
  assumption.
  apply IHenv1A. 
  assumption.
  assumption.
Defined.  


Lemma overrideEnvLemmaT {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type): 
     forall (env1A env1B: Envr K V1) (env2A env2B: Envr K V2), 
  MatchEnvsT rel env1A env2A ->
  MatchEnvsT rel env1B env2B -> 
  MatchEnvsT rel (overrideE env1A env1B) (overrideE env2A env2B).  
Proof.
  unfold overrideE.
  eapply appEnvLemmaT.
Defined.




Lemma RelatedByEnvEP_T {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type) 
                     (env1: Envr K V1) (env2: Envr K V2) (x: K)
                     (v1: V1) (v2: V2)
         : MatchEnvsT rel env1 env2 -> findET env1 x v1 ->
           findET env2 x v2 -> rel v1 v2.
Proof.
  intros.
  rename X0 into H0.
  rename X1 into H1.
  rename X into H.
  inversion H0; subst.
  inversion H1; subst.
  induction H. 
  inversion H2.
  inversion H3; subst.
  inversion H2; subst.
  destruct (dEq x k).
  inversion H6; subst.
  inversion H5; subst.
  assumption.
  apply IHMatchEnvsT.
  constructor.
  assumption.
  constructor.  
  assumption.
  assumption.
  assumption.
Defined.


(*******************)



Lemma ExRelValT {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Type)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2): 
    MatchEnvsT R venv tenv ->
    findET tenv x t ->
    sigT2 (findET venv x) (fun v: V1 => R v t). 
Proof.
  intros.
  induction X; subst.
  inversion X0.
  inversion H.
  inversion X0; subst.
  inversion H; subst.
  rename v2 into t2.
  destruct (dEq x k). 
  inversion H1; subst.
(*
  inversion X0; subst.
  inversion H0; subst.
  destruct (dEq k k).
*)  
  econstructor.
  instantiate (1:= v1).
  constructor.
  simpl.
  destruct (dEq k k).
  auto.
  intuition n.
  assumption.
  assert (findET ls2 x t).
  constructor.
  auto.
  eapply IHX in X1.
  destruct X1.
(*  destruct p. *)
  econstructor.
  instantiate (1:= x0).
(*  split. *)
  constructor.  
  simpl.
  destruct (dEq x k).
  rewrite e in n.
  intuition n.
  inversion f; subst.
  assumption.
  assumption.
Defined.

(*
Lemma ExRelValT {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Type)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2): 
    MatchEnvsT R venv tenv ->
    findET tenv x t ->
    sigT (fun v: V1 => (prod (findET venv x v) (R v t))). 
Proof.
  intros.
  induction X; subst.
  inversion X0.
  inversion H.
  inversion X0; subst.
  inversion H; subst.
  rename v2 into t2.
  destruct (dEq x k). 
  inversion H1; subst.
  econstructor.
  instantiate (1:= v1).
  split.
  constructor.
  simpl.
  destruct (dEq k k).
  auto.
  intuition n.
  assumption.
  assert (findET ls2 x t).
  constructor.
  auto.
  eapply IHX in X1.
  destruct X1.
  destruct p.
  econstructor.
  instantiate (1:= x0).
  split.
  constructor.  
  simpl.
  destruct (dEq x k).
  rewrite e in n.
  intuition n.
  inversion f; subst.
  assumption.
  assumption.
Defined.
*)


Lemma ExRelValTNone {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Type)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2): 
    MatchEnvsT R venv tenv ->
    findE tenv x = None ->
    findE venv x = None.
Proof.
  intros.
  induction X; subst.
  simpl.
  reflexivity.
  inversion H; subst.
  simpl.
  destruct (dEq x k).
  inversion H1.
  apply IHX.
  assumption.
Defined.  


Definition ExRelValTProj1 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Type)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2) 
       (h1: MatchEnvsT R venv tenv)
       (h2: findET tenv x t) :
  sigT (fun v: V1 => findET venv x v) :=
        sigT_of_sigT2 (ExRelValT R tenv venv x t h1 h2).


Definition snd_sigT_of_sigT2 {A : Type} {P Q : A -> Type} (X : sigT2 P Q) :
   sigT Q
  := existT Q
            (let (a, _, _) := X in a)
            (let (x, _, q) as s return (Q (let (a, _, _) := s in a)) := X in q).

Definition proj1_of_sigT2 {A : Type} {P Q : A -> Type} (X : sigT2 P Q) : A :=
           (projT1 (sigT_of_sigT2 X)).


Definition ExRelValTProj2 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Type)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2) 
       (h1: MatchEnvsT R venv tenv)
       (h2: findET tenv x t) := 
        snd_sigT_of_sigT2 (ExRelValT R tenv venv x t h1 h2).


Inductive Forall2T {A B : Type} (R: A -> B -> Type): 
    list A -> list B -> Type := 
  | Forall2_nilT : Forall2T R nil nil
  | Forall2_consT : forall x y l l',
      R x y -> Forall2T R l l' -> Forall2T R (x::l) (y::l').

Inductive ForallT {A: Type} (P: A -> Type): list A -> Type :=
      | Forall_nilT : ForallT P nil
      | Forall_consT : forall x l, P x -> ForallT P l -> ForallT P (x::l).


(***********************************************)


Lemma findEP2extCons2 {K V: Type} {h: DEq K} (env: Envr K V) (x y: K)
      (u v: V):
    x <> y -> findET2 (updateE env y v) x u -> findET2 env x u. 
  intros.
  rename X into H0.
  inversion H0; subst.
  unfold updateE in H1.
  unfold overrideE in H1.
  destruct m0.
  simpl in H1.
  inversion H1; subst.
  intuition H.
  inversion H1; subst.
  simpl in H1.

  econstructor.
  instantiate (1:= m1).
  unfold overrideE.
  unfold updateE.
  reflexivity.

  eapply findEextCons in H.
  rewrite H.
  eassumption.
Defined.


Lemma findEP2toEP_T {K V: Type} {h: DEq K} (env: Envr K V) (x: K) (v: V):
  findET2 env x v -> findET env x v.
Proof.
intros.
rename X into H.
inversion H; subst.  
constructor.
revert H.
revert H1.
revert m1.
induction m0.
intros.
simpl.
destruct (dEq x x).
reflexivity.
intuition n.
simpl.
destruct a.
destruct (dEq x k).
intros.
inversion H1.
intros.
specialize (IHm0 m1 H1).
eapply findEP2extCons2 with (env := (overrideE m0 (updateE m1 x v))) in n.
eapply IHm0 in n.

assumption.
unfold updateE.
eassumption.
Defined.


Lemma RelatedByEnvEP2_T {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Type) 
                     (env1: Envr K V1) (env2: Envr K V2) (x: K)
                     (v1: V1) (v2: V2)
         : MatchEnvsT rel env1 env2 -> findET2 env1 x v1 ->
           findET2 env2 x v2 -> rel v1 v2.
intros.
apply findEP2toEP_T in X0.
apply findEP2toEP_T in X1.
eapply RelatedByEnvEP_T.
eassumption.
eassumption.
assumption.
Defined.

(*******************************************************************)


Fixpoint interleave {V1 V2: Type} (ls1 : list V1) (ls2: list V2) :
                                                    list (V1 * V2) :=
  match ls1 with
    | nil => nil 
    | cons x ts1 => match ls2 with
               | nil => nil          
               | cons y ts2 => cons (x,y) (interleave ts1 ts2)
               end                                   
  end.


Lemma listLengthAux1 {A B: Type} (ls1 : list A) (ls2 : list B) :
      (length ls1 = length ls2) -> ls2 = map snd (interleave ls1 ls2).
Proof.
  revert ls1.
  induction ls2.
  intros.  
  assert (interleave ls1 nil = @nil (prod A B)).
  induction ls1.
  simpl.
  auto.  
  simpl.
  auto.
  rewrite H0.
  simpl.
  auto.
  simpl.
  destruct ls1.
  simpl.
  intros.
  inversion H.
  simpl.
  intros.
  inversion H; subst.
  eapply IHls2 in H1.
  rewrite <- H1.
  auto.
Defined.  



Lemma prmsTypingAux1_T {A T V: Type} (R: V -> T -> Type)
        (fps : list (A * T)) (vls : list V)
        (h2: length fps = length vls):
  Forall2T R vls (map snd fps) ->
  Forall2T R (map snd (interleave (map fst fps) vls))
               (map snd fps).
Proof.
  assert (length (map fst fps) = length vls).
  symmetry.
  rewrite <- h2.
  eapply map_length.
  intros.
  generalize H.
  intros.
  eapply listLengthAux1 in H0.
  rewrite <- H0.
  auto.
Defined.


Lemma prmsTypingAux2_T {A T V: Type} {h: DEq A} (R: V -> T -> Type)
      (fps : list (A * T)) (vls : list V) 
      (h2: length fps = length vls):
  (Forall2T R (map snd (interleave (map fst fps) vls))
                (map snd fps)) ->
  (MatchEnvsT R (interleave (map fst fps) vls) fps).        
Proof.
  assert (length (map fst fps) = length vls).
  symmetry.
  rewrite <- h2.
  eapply map_length.
  eapply listLengthAux1 in H.
  rewrite <- H.
  intro.
  dependent induction X.
  simpl in h2.
  eapply length_zero_iff_nil in h2.
  inversion h2; subst.
  simpl.
  constructor.
  destruct fps.
  simpl in h2.
  inversion h2.
  simpl.
  simpl in h2.
  inversion h2; subst.
  simpl in H.
  inversion H; subst.
  simpl in x.
  inversion x; subst.
  destruct p.
  simpl in r.
  simpl.
  econstructor.
  assumption.
  rewrite <- H2.
  eapply IHX.
  auto.
  auto.
  auto.
Defined.  

(************************************)

Lemma sameBehSameLength_T {A B: Type} (R : A -> B -> Type)
        (ls1: list A) (ls2: list B) : Forall2T R ls1 ls2 ->
            length ls1 = length ls2.                            
Proof.
  intros.
  induction X.
  reflexivity. 
  simpl.
  auto.
Defined.  



(*
Inductive MatchListsT {V1 V2: Type} (rel: V1 -> V2 -> Type) : 
          list V1 -> list V2 -> Type :=
| MatchListsT_Nil : MatchListsT rel nil nil
| MatchListsT_Cons : forall ls1 ls2 v1 v2,
                     rel v1 v2 ->
                     MatchListsT rel ls1 ls2 ->
            MatchListsT rel (v1::ls1) (v2::ls2).                          


Lemma prmsTypingAux1_T {A T V: Type} (R: V -> T -> Type)
        (fps : list (A * T)) (vls : list V)
        (h2: length fps = length vls):
  MatchListsT R vls (map snd fps) ->
  MatchListsT R (map snd (interleave (map fst fps) vls))
               (map snd fps).
Proof.
  assert (length (map fst fps) = length vls).
  symmetry.
  rewrite <- h2.
  eapply map_length.
  intros.
  generalize H.
  intros.
  eapply listLengthAux1 in H0.
  rewrite <- H0.
  auto.
Qed.
  

                                            
Lemma prmsTypingAux2_T {A T V: Type} {h: DEq A} (R: V -> T -> Type)
      (fps : list (A * T)) (vls : list V) 
      (h2: length fps = length vls):
  (MatchListsT R (map snd (interleave (map fst fps) vls))
                (map snd fps)) ->
  (MatchEnvsT R (interleave (map fst fps) vls) fps).        
Proof.
  assert (length (map fst fps) = length vls).
  symmetry.
  rewrite <- h2.
  eapply map_length.
  eapply listLengthAux1 in H.
  rewrite <- H.
  intro.
  dependent induction X.
  simpl in h2.
  eapply length_zero_iff_nil in h2.
  inversion h2; subst.
  simpl.
  constructor.
  destruct fps.
  simpl in h2.
  inversion h2.
  simpl.
  simpl in h2.
  inversion h2; subst.
  simpl in H.
  inversion H; subst.
  simpl in x.
  inversion x; subst.
  destruct p.
  simpl in r.
  simpl.
  econstructor.
  assumption.
  rewrite <- H2.
  eapply IHX.
  auto.
  auto.
  auto.
Qed.  

*)
