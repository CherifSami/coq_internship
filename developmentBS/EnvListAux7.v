

Require Export Basics.
Require Export Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.

Require Import Coq.Logic.ProofIrrelevance.
Require Export Coq.Structures.Equalities.


(** decidable equality class *)

Class DEq (K: Type) : Type := {
   dEq : forall x y: K, {x = y} + {x <> y}
}.  


(** general environment type - partial maps *)

Definition genEnv (K V: Type) : Type := list (K * V).


Definition Envr (K V: Type) : Type := list (K * V).

Fixpoint findE {K V: Type} {h: DEq K} (m: Envr K V) (k: K) : option V :=
  match m with
     | nil => None
     | cons (k', x) ls => match (dEq k k') with
                            | left _ => Some x
                            | right _ => findE ls k
                            end               
    end.

Inductive findEP {K V: Type} {h: DEq K} (m: Envr K V) (k: K) : V -> Prop :=
  FindEP : forall x: V, findE m k = Some x -> findEP m k x.

Definition emptyE {K V: Type}: Envr K V := nil.

Definition overrideE {K V: Type}  
    (f1 f2: Envr K V) : Envr K V := app f1 f2.

Definition updateE {K V: Type} (g: Envr K V) (z: K) (t: V) :
    Envr K V := cons (z, t) g.

Definition singleE {K V: Type} (z: K) (t: V) : 
   Envr K V := cons (z, t) emptyE. 

Definition findED2 {K V: Type} {h: DEq K} (m m0 m1: Envr K V)
                    (k: K) (v: V) : Prop := 
            m = overrideE m0 (updateE m1 k v) /\ findE m0 k = None.

Inductive findEP2 {K V: Type} {h: DEq K} (m: Envr K V) (k: K) : V -> Prop :=
  FindEP2 : forall (v: V) (m0 m1: Envr K V),
            m = overrideE m0 (updateE m1 k v) ->  
            findE m0 k = None ->  
            findEP2 m k v.


Inductive disjoint {K V: Type} {h: DEq K} (m1 m2: Envr K V) : Prop :=
   disjoint1 : (forall x: K, or (findE m1 x = None) (findE m2 x = None)) -> 
                   disjoint m1 m2.


Inductive includeEnv {K V: Type} {h: DEq K} (m1 m2: Envr K V) : Prop :=
  includeEnv1 : (forall x: K, or (findE m1 x = None)
                                 (findE m1 x = findE m2 x)) -> 
                   includeEnv m1 m2.



(** lifting for option types *)

Inductive liftEq (T: Type) : (option T) -> T -> Prop := 
   | LiftEq : forall e:T, liftEq T (Some e) e.

Inductive liftWkEq (T: Type) : (option T) -> T -> Prop := 
   | LiftWkEq1 : forall e:T, liftWkEq T (Some e) e
   | LiftWkEq2 : forall e:T, liftWkEq T None e.

Definition liftM (X Y: Type) (f: X -> Y) (x:option X) : option Y :=
   match x with
   | Some x1 => Some (f x1)
   | None => None
   end.

Definition lift2M (X Y Z: Type) (f: X -> Y -> Z) (x:option X) (y:option Y) : 
 option Z :=
   match x,y with
   | Some x1, Some y1 => Some (f x1 y1)
   | _,None => None
   | None,_ => None
   end.


(************************************************************************)

Lemma overrideAssoc (K V: Type) (env1 env2 env3: Envr K V) :
          (overrideE env1 (overrideE env2 env3)) =
          (overrideE (overrideE env1 env2) env3).
Proof.
  unfold overrideE.  
  rewrite app_assoc.
  reflexivity.
Defined.


Lemma find_simpl {K V: Type} {h: DEq K}
      (env: Envr K V) (x: K) (v: V) :
  findE ((x, v)::env) x = Some v.
  simpl.
  destruct (dEq x x).
  auto.
  intuition n.
Defined.  


Lemma find_persists1 {K V: Type} {h: DEq K}
      (env1 env2: Envr K V) (x y: K) (v: V) :
  findE env1 y = findE env2 y ->
  findE (updateE env1 x v) y = findE (updateE env2 x v) y. 
Proof.
  intros.
  simpl.
  destruct (dEq y x).
  auto.
  auto.
Defined.  

Lemma find_persists2 {K V: Type} {h: DEq K}
      (env: Envr K V) (x y: K) (v: V) :
  findE (updateE env x v) y = None ->
  findE env y = None.
  simpl.
  intros.
  destruct (dEq y x) in H.
  inversion H.
  auto.
Defined.  

Lemma find_persists3 {K V: Type} {h: DEq K}
      (env: Envr K V) (x y: K) (v: V) :
  findE (updateE env x v) y = None ->
  x <> y.
  simpl.
  intros.
  destruct (dEq y x) in H.
  inversion H.
  auto.
Defined.  

Lemma find_persists4 {K V: Type} {h: DEq K}
      (env: Envr K V) (x y: K) (v: V) :
  x <> y -> findE (updateE env x v) y = findE env y. 
  intros.
  simpl.
  destruct (dEq y x).
  rewrite e in H.
  intuition.
  auto.
Defined.


Lemma overrideRedux1 {K V: Type} {h: DEq K}
      (env1 env2: Envr K V) (x: K) (v: V) :
  findE env1 x = Some v -> findE (overrideE env1 env2) x = findE env1 x.
Proof.
  induction env1.
  intros.
  simpl in H.
  inversion H.
  destruct a.
  simpl.
  destruct (dEq x k).
  auto.
  auto.
Defined.

Lemma overrideRedux2 {K V: Type} {h: DEq K}
      (env1 env2: Envr K V) (x: K) :
  findE env1 x = None -> findE (overrideE env1 env2) x = findE env2 x.
Proof.
  induction env1.
  intros.
  unfold overrideE.
  rewrite app_nil_l.
  auto.
  destruct a.
  intros.
  set (G := (findE ((k, v) :: env1) x = None)).
  assert G.
  auto.
  assert G.
  auto.
  apply find_persists2 in H0.
  apply find_persists3 in H1.
  set (J := (findE env1 x = None)).
  assert J.
  auto.
  unfold overrideE.
  rewrite <- app_comm_cons.
  apply IHenv1 in H2.  
  eapply find_persists4 in H1.
  unfold updateE in H1.
  erewrite H1.
  apply IHenv1 in H0.
  auto.
Defined.
  

(*************************************************************************)

(*
 Inductive MatchOptions {V1 V2: Type} (rel: V1 -> V2 -> Prop) : 
                 option V1 -> option V2 -> Prop :=
  | Some_MO : forall (x1: V1) (x2: V2),
                 rel x1 x2 -> MatchOptions rel (Some x1) (Some x2)
  | None_MO : MatchOptions rel None None.                                       *)         

Inductive LiftRel {A B: Type} (R: A -> B -> Prop) :
                       option A -> option B -> Prop :=
| SLift : forall (v: A) (t: B), R v t ->
                          LiftRel R (Some v) (Some t)                 
| NLift : LiftRel R None None. 

Inductive MatchEnvs {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop) : 
          Envr K V1 -> Envr K V2 -> Prop :=
| MatchEnvs_Nil : MatchEnvs rel nil nil
| MatchEnvs_Cons : forall ls1 ls2 k v1 v2,
                     rel v1 v2 ->
                     MatchEnvs rel ls1 ls2 ->
                     MatchEnvs rel ((k,v1)::ls1) ((k,v2)::ls2).

Inductive MatchEnvs2 {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop) : 
          Envr K V1 -> Envr K V2 -> Prop :=
| MatchEnvs2_Nil : MatchEnvs2 rel nil nil
| MatchEnvs2_Cons : forall ls5 ls6 ls1 ls2 ls3 ls4 k v1 v2,
                     rel v1 v2 ->
                     MatchEnvs rel ls1 ls2 ->
                     MatchEnvs rel ls3 ls4 ->
                     findE ls2 k = None ->
                     ls5 = ls1 ++ ((k,v1)::ls3) ->
                     ls6 = ls2 ++ ((k,v2)::ls4) ->
            MatchEnvs2 rel ls5 ls6.                         


Inductive MatchEnvs2B {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop)  
          (k: K) (v1: V1) (v2: V2) : Envr K V1 -> Envr K V2 -> Prop :=
| MatchEnvs2B_split : forall ls5 ls6 ls1 ls2 ls3 ls4,
                     rel v1 v2 ->
                     MatchEnvs rel ls1 ls2 ->
                     MatchEnvs rel ls3 ls4 ->
                     findE ls2 k = None -> 
                     ls5 = ls1 ++ ((k,v1)::ls3) ->
                     ls6 = ls2 ++ ((k,v2)::ls4) ->
            MatchEnvs2B rel k v1 v2 ls5 ls6.                         


Inductive MatchLists {V1 V2: Type} (rel: V1 -> V2 -> Prop) : 
          list V1 -> list V2 -> Prop :=
| MatchLists_Nil : MatchLists rel nil nil
| MatchLists_Cons : forall ls1 ls2 v1 v2,
                     rel v1 v2 ->
                     MatchLists rel ls1 ls2 ->
            MatchLists rel (v1::ls1) (v2::ls2).                          

(*
Definition VectorMapRel (V1 V2: Type) (R: V1 -> V2 -> Prop) (n: nat) 
   (a1: t V1 n) (a2: t V2 n) : Prop :=
   forall i: Fin.t n, R (nth a1 i) (nth a2 i). 
*)
(*********************************************************************)


Lemma consEnvLemma {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop)
              (env1: Envr K V1) (env2: Envr K V2) (x: K)
                      (v1: V1) (v2: V2):
    MatchEnvs rel env1 env2 ->
    rel v1 v2 -> 
    MatchEnvs rel ((x, v1)::env1) ((x, v2)::env2).  
Proof.
  intros.
  constructor.
  assumption.
  assumption.
Defined.


Lemma updateEnvLemma {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop)
              (env1: Envr K V1) (env2: Envr K V2) (x: K)
                      (v1: V1) (v2: V2):
    MatchEnvs rel env1 env2 ->
    rel v1 v2 -> 
    MatchEnvs rel (updateE env1 x v1) (updateE env2 x v2).  
Proof.
  unfold updateE.
  eapply consEnvLemma. 
Defined.


Lemma app_cons_assoc {A: Type} (x: A) (ls1 ls2: list A):
       (x :: ls1) ++ ls2 = x :: (ls1 ++ ls2).
Proof.
simpl.
reflexivity.
Defined.


Lemma appEnvLemma {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop): 
     forall (env1A env1B: Envr K V1) (env2A env2B: Envr K V2), 
  MatchEnvs rel env1A env2A ->
  MatchEnvs rel env1B env2B -> 
  MatchEnvs rel (env1A ++ env1B) (env2A ++ env2B).  
Proof.
  induction env1A.
  intros. 
  induction env2A.
  simpl.
  assumption.
  inversion H.  
  induction env2A.
  intros.
  inversion H.  
  intros.
  simpl.
  destruct a.
  destruct a0.
  destruct (dEq k k0).
  Focus 2.
  inversion H; subst.  
  intuition n.
  destruct e.
  inversion H; subst.
  constructor.
  assumption.
  apply IHenv1A. 
  assumption.
  assumption.
Defined.  


Lemma overrideEnvLemma {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop): 
     forall (env1A env1B: Envr K V1) (env2A env2B: Envr K V2), 
  MatchEnvs rel env1A env2A ->
  MatchEnvs rel env1B env2B -> 
  MatchEnvs rel (overrideE env1A env1B) (overrideE env2A env2B).  
Proof.
  unfold overrideE.
  eapply appEnvLemma.
Defined.


Lemma MatchEnvs1to2 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)  
          (env1: Envr K V1) (env2: Envr K V2) :
  MatchEnvs R env1 env2 -> MatchEnvs2 R env1 env2. 
intros.
inversion H; subst.  
constructor.
eapply MatchEnvs2_Cons.
eassumption.
eapply MatchEnvs_Nil.
eapply H1.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
Defined.


Lemma MatchEnvs2to1 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)  
          (env1: Envr K V1) (env2: Envr K V2) :
  MatchEnvs2 R env1 env2 -> MatchEnvs R env1 env2.
  intros.
  inversion H; subst.
  constructor.
  destruct ls1.
  destruct ls2.
  simpl.
  constructor.
  assumption.
  assumption.
  inversion H1.
  destruct ls2.
  inversion H1.
  rewrite <- app_comm_cons.
  rewrite <- app_comm_cons.
  destruct p.  
  destruct p0.
  inversion H1; subst.
  eapply MatchEnvs_Cons.
  assumption.

  eapply appEnvLemma.   
  assumption.
  eapply consEnvLemma.
  assumption.
  assumption.
Defined.


Lemma findEPAbs {K V: Type} {h: DEq K} (x: K) (v: V):
    findEP2 nil x v -> False.
  intros.
  inversion H; subst.
  unfold overrideE in H0.
  unfold updateE in H0.
  destruct m0.
  simpl in H0.
  inversion H0.
  inversion H0.
Defined.

Lemma findEPbreak  {K V: Type} {h: DEq K} (env: Envr K V) (x: K) (v: V):
  findEP env x v -> exists (env0 env1: Envr K V),
       env = overrideE env0 (updateE env1 x v) /\ findE env0 x = None.  
intros.
inversion H; subst.
dependent induction env. 
inversion H0.

simpl in H0.
destruct a as [x0 v0].
destruct (dEq x x0).
inversion e; subst.
exists nil.
exists env.
split.
simpl.
unfold updateE.
inversion H0; subst.
reflexivity.
simpl.
reflexivity.

specialize (IHenv x v). 
assert (findEP env x v).
constructor.
assumption.
specialize (IHenv H1 H0).
destruct IHenv as [env0].
destruct H2 as [env1].
destruct H2.
eexists ((x0,v0)::env0).
eexists env1.
simpl.
split.
rewrite H2.
reflexivity.
destruct (dEq x x0).
rewrite e in n.
intuition n.
assumption.
Defined.


Lemma findEextCons {K V: Type} {h: DEq K} (env: Envr K V) (x y: K) (v: V):
    x <> y -> findE env x = findE (updateE env y v) x. 
intros.
induction env.
simpl.
destruct (dEq x y).
rewrite e in H.
intuition.
reflexivity.
simpl.
destruct a.
simpl in IHenv.
revert IHenv.
destruct (dEq x y).
rewrite e in H.
intuition H.
intros.
reflexivity.
Defined.

Lemma findEexApp {K V: Type} {h: DEq K} (env env0: Envr K V) (x: K):
    findE env0 x = None -> findE env x = findE (overrideE env0 env) x. 
intros.
induction env.
simpl.
unfold overrideE.  
rewrite app_nil_r.
symmetry.
assumption.
destruct a.
revert IHenv.
simpl.
revert H.
induction env0.
unfold overrideE.
simpl.
intros.
reflexivity.
destruct a.
simpl.
destruct (dEq x k0).
intros.
inversion H.
intros.
destruct (dEq x k).
apply IHenv0.
assumption.
assumption.
apply IHenv0.
assumption.
assumption.
Defined.

Lemma findEP2extCons1 {K V: Type} {h: DEq K} (env: Envr K V) (x y: K)
      (u v: V):
    x <> y -> findEP2 env x u -> findEP2 (updateE env y v) x u. 
  intros.
  inversion H0; subst.
  econstructor.
  unfold updateE.
  unfold overrideE.
  eapply app_comm_cons.
  rewrite <- H2.
  symmetry.
  eapply findEextCons.
  assumption.
Defined.

Lemma findEP2extCons2 {K V: Type} {h: DEq K} (env: Envr K V) (x y: K)
      (u v: V):
    x <> y -> findEP2 (updateE env y v) x u -> findEP2 env x u. 
  intros.
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

 
Lemma findEPtoEP2  {K V: Type} {h: DEq K} (env: Envr K V) (x: K) (v: V):
   findEP env x v -> findEP2 env x v.
intros.
inversion H; subst.
eapply (findEPbreak) in H.
destruct H.
destruct H.
destruct H.
econstructor.
eassumption.
assumption.
Defined.

Lemma findEP2toEP  {K V: Type} {h: DEq K} (env: Envr K V) (x: K) (v: V):
  findEP2 env x v -> findEP env x v.
intros.
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


Lemma RelatedByEnvEP {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop) 
                     (env1: Envr K V1) (env2: Envr K V2) (x: K)
                     (v1: V1) (v2: V2)
         : MatchEnvs rel env1 env2 -> findEP env1 x v1 ->
           findEP env2 x v2 -> rel v1 v2.
Proof.
  intros.
  inversion H0; subst.
  inversion H1; subst.
  induction H. 
  inversion H2.
  inversion H3; subst.
  inversion H2; subst.
  destruct (dEq x k).
  inversion H6; subst.
  inversion H7; subst.
  assumption.
  apply IHMatchEnvs.
  constructor.
  assumption.
  constructor.  
  assumption.
  assumption.
  assumption.
Defined.


Lemma RelatedByEnvEP2 {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop) 
                     (env1: Envr K V1) (env2: Envr K V2) (x: K)
                     (v1: V1) (v2: V2)
         : MatchEnvs rel env1 env2 -> findEP2 env1 x v1 ->
           findEP2 env2 x v2 -> rel v1 v2.
intros.
apply findEP2toEP in H0.
apply findEP2toEP in H1.
eapply RelatedByEnvEP.
eassumption.
eassumption.
assumption.
Defined.



(*******************)

Lemma derive_absurd1 {V: Type} (ls: list V) (p: length ls > 0) :
  ls = nil -> False.
  intros.
  rewrite H in p.
  compute in p.
  inversion p.
Defined.  
  
Definition hd_total {V: Type} (ls: list V) : (length ls > 0) -> V :=
  match ls with
      | nil => (fun p => match (derive_absurd1 nil p eq_refl) with end)
      | cons x ts => fun _ => x
  end.                 

Lemma tl_length {V1 V2: Type} (ls1: list V1) (ls2: list V2)
      (p: length ls1 = length ls2) :
  length (tl ls1) = length (tl ls2).
  induction ls2.
  induction ls1.
  compute.
  reflexivity.
  simpl in p.
  inversion p.
  simpl in p.
  simpl.
  assert (length ls1 > 0 -> length ls1 = S (length (tl ls1))).
  intros.
  induction ls1.
  inversion H.
  simpl.
  reflexivity.
  assert (length ls1 > 0).
  rewrite p at 1.
  omega.
  apply H in H0.
  rewrite p in H0.
  inversion H0; subst.
  reflexivity.
Defined.  

Lemma cons_length {V1 V2: Type} (ls1: list V1) (ls2: list V2)
      (x: V1) (y: V2)  
      (p: length (cons x ls1) = length (cons y ls2)) :
  length ls1 = length ls2.
  simpl in p.
  inversion p.
  reflexivity.
Defined.  


Lemma derive_absurd2r {V1 V2: Type} (ls: list V2) (x: V2) :
  (length (@nil V1) = length (cons x ls)) -> False.
  intros.
  inversion H.
Defined.

Lemma derive_absurd2l {V1 V2: Type} (ls: list V1) (x: V1) :
  (length (cons x ls) = length (@nil V2)) -> False.
  intros.
  inversion H.
Defined.


Fixpoint zip {V1 V2: Type} (ls1 : list V1) (ls2: list V2) :
           (length ls1 = length ls2) -> list (V1 * V2) :=
  match ls1 with
    | nil => match ls2 with
               | nil => fun _ => nil
               | cons _ _ => fun p => match (derive_absurd2r _ _ p) with end
               end
    | cons x ts1 => match ls2 with
               | nil => fun p => match (derive_absurd2l _ _ p) with end          
               | cons y ts2 => fun p => cons (x,y) 
                      (zip ts1 ts2 (cons_length ts1 ts2 x y p))
               end                                   
  end.

Extraction zip.

Lemma map_length {V1 V2: Type} (ls: list V1) (f: V1 -> V2) :
  length ls = length (map f ls).
  induction ls.
  simpl.
  reflexivity.
  simpl.
  rewrite IHls.
  reflexivity.
Defined.  
  

Lemma map_fst_length {V1 V2 V3: Type} (ls1: list (V1 * V2)) (ls2: list V3) :
  length ls1 = length ls2 -> length (map fst ls1) = length ls2.
  intros.
  erewrite <- map_length.
  assumption.
Defined.  


Lemma nthErrorAux1 {A: Type} : forall n:nat, @nth_error A nil n = None.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Defined.  


Lemma nthErrorAux2 {A: Type} (a: A) (ls: list A):
                @nth_error A (a::ls) 0 = Some a.
  compute.
  reflexivity.
Defined.  


Lemma nthErrorAux3 {A B: Type} (R : A -> B -> Prop)
        (ls1: list A) (ls2: list B) (a: A) (b: B): (forall n : nat,
    LiftRel R (nth_error (a :: ls1) n) (nth_error (b :: ls2) n)) ->
  (forall n : nat, LiftRel R (nth_error ls1 n) (nth_error ls2 n)).
Proof.
intros.
specialize (H (S n)).
simpl in H.
assumption.
Defined.


Lemma sameBehSameLength {A B: Type} (R : A -> B -> Prop)
        (ls1: list A) (ls2: list B) : MatchLists R ls1 ls2 ->
            length ls1 = length ls2.                            
Proof.
  intros.
  induction H.
  reflexivity. 
  simpl.
  auto.
Defined.  


Lemma sameBehSameLengthB {A B: Type} (R : A -> B -> Prop)
        (ls1: list A) (ls2: list B) : (forall n : nat,
          LiftRel R (nth_error ls1 n) (nth_error ls2 n)) ->
            length ls1 = length ls2.                            
Proof.
  intros.
  dependent induction ls1.
  dependent induction ls2.
  reflexivity.
  specialize (H 0).
  simpl in H.
  inversion H; subst.
  dependent induction ls2.
  specialize (H 0).
  simpl in H.
  inversion H.  
  specialize (IHls1 ls2).
  assert ((forall n : nat,
    LiftRel R (nth_error (a :: ls1) n) (nth_error (a0 :: ls2) n)) ->
  (forall n : nat, LiftRel R (nth_error ls1 n) (nth_error ls2 n))). 
  apply (nthErrorAux3 R ls1 ls2 a a0).
  assert (forall n : nat, LiftRel R (nth_error ls1 n) (nth_error ls2 n)).
  auto.
  apply IHls1 in H1.
  simpl.
  auto.
Defined.
  


Lemma ExRelVal {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2): 
    MatchEnvs R venv tenv ->
    findEP tenv x t ->
    exists v: V1, findEP venv x v /\ R v t. 
Proof.
  intros.
  induction H; subst.
  inversion H0.
  inversion H.
  inversion H0; subst.
  inversion H2; subst.
  rename v2 into t2.
  destruct (dEq x k). 
  inversion H4; subst.
  exists v1.
  split.
  constructor.
  simpl.
  destruct (dEq k k).
  auto.
  intuition n.
  assumption.
  assert (findEP ls2 x t).
  constructor.
  auto.
  eapply IHMatchEnvs in H3.
  destruct H3.
  destruct H3.
  exists x0.
  split.
  constructor.  
  simpl.
  destruct (dEq x k).
  rewrite e in n.
  intuition n.
  inversion H3; subst.
  assumption.
  assumption.
Defined.


Lemma ExRelValRev {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (v: V1): 
    MatchEnvs R venv tenv ->
    findEP venv x v ->
    exists t: V2, findEP tenv x t /\ R v t. 
Proof.
  intros.
  induction H; subst.
  inversion H0.
  inversion H.
  inversion H0; subst.
  inversion H2; subst.
  rename v2 into t1.
  destruct (dEq x k). 
  inversion H4; subst.
  exists t1.
  split.
  constructor.
  simpl.
  destruct (dEq k k).
  auto.
  intuition n.
  assumption.
  assert (findEP ls1 x v).
  constructor.
  auto.
  eapply IHMatchEnvs in H3.
  destruct H3.
  destruct H3.
  exists x0.
  split.
  constructor.  
  simpl.
  destruct (dEq x k).
  rewrite e in n.
  intuition n.
  inversion H3; subst.
  assumption.
  assumption.
Defined.


Lemma ExRelValNone {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2): 
    MatchEnvs R venv tenv ->
    findE tenv x = None ->
    findE venv x = None.
Proof.
  intros.
  induction H; subst.
  simpl.
  reflexivity.
  inversion H0; subst.
  simpl.
  destruct (dEq x k).
  inversion H3.
  apply IHMatchEnvs.
  assumption.
Defined.  


Lemma ExRelValProj1 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
       (tenv: Envr K V2) (venv: Envr K V1) (x: K) (t: V2): 
    MatchEnvs R venv tenv ->
    findEP tenv x t ->
    exists v: V1, findEP venv x v.
Proof.
  intros.
  eapply ExRelVal in H. 
  destruct H.
  destruct H.
  eexists.
  eauto.
  eauto.
Defined.
  


Inductive Forall3A {A B :Type} (R: A -> B -> Prop)
          (P: forall (a:A) (b:B), R a b -> Type) :
           list A -> list B -> Prop :=
| Forall3A_nil : Forall3A R P nil nil
| Forall3A_cons : forall (aas: list A) (bbs: list B) 
                        (a:A) (b:B) (p: R a b),
                   P a b p ->
                   Forall3A R P aas bbs ->                          
                   Forall3A R P (a::aas) (b::bbs).              


Inductive Forall3 {K A B :Type} (R: A -> B -> Prop)
          (P: forall (a:A) (b:B), R a b -> Prop) :
           Envr K A -> Envr K B -> Prop :=
| Forall3_nil : Forall3 R P nil nil
| Forall3_cons : forall (aas: Envr K A) (bbs: Envr K B) 
                        (x:K) (a:A) (b:B) (p: R a b),
                   P a b p ->
                   Forall3 R P aas bbs ->                          
                   Forall3 R P ((x,a)::aas) ((x,b)::bbs).              



Inductive Forall2B {K A B :Type} {h: DEq K} (R: A -> B -> Prop)
          (P: forall (a:A) (b:B), R a b -> Prop)
          (Q: forall (ls1: Envr K A) (ls2: Envr K B),
                     MatchEnvs R ls1 ls2 -> Prop) :
          K -> A -> B -> Envr K A -> Envr K B -> Prop :=
 Forall2B_split : forall (aas as1 as2: Envr K A)
                         (bbs bs1 bs2: Envr K B) 
                         (k:K) (a:A) (b:B)
                         (p1: MatchEnvs R as1 bs1)
                         (p2: MatchEnvs R as2 bs2)
                         (p0: R a b),
                 aas = as1 ++ ((k,a)::as2) ->
                 bbs = bs1 ++ ((k,b)::bs2) ->
                 Q as1 bs1 p1 ->
                 Q as2 bs2 p2 ->
                 P a b p0 -> 
                 Forall2B R P Q k a b aas bbs. 


Inductive Forall2BC {K A B :Type} {h: DEq K} (R: A -> B -> Prop)
          (P: forall (ls1: Envr K A) (ls2: Envr K B),
                     MatchEnvs R ls1 ls2 -> Prop) :
          K -> A -> B -> Envr K A -> Envr K B -> Prop :=
 Forall2BC_split : forall (aas as1 as2: Envr K A)
                         (bbs bs1 bs2: Envr K B) 
                         (k:K) (a:A) (b:B)
                         (p1: MatchEnvs R as1 bs1)
                         (p2: MatchEnvs R as2 bs2)
                         (p0: MatchEnvs R (singleE k a) (singleE k b)),
                 aas = as1 ++ ((k,a)::as2) ->
                 bbs = bs1 ++ ((k,b)::bs2) ->
                 P as1 bs1 p1 ->
                 P as2 bs2 p2 ->
                 P (singleE k a) (singleE k b) p0 -> 
                 Forall2BC R P k a b aas bbs. 


Lemma matchForallAux1 {K A B} {h: DEq K} (R: A -> B -> Prop)
      (P: forall (a:A) (b:B), R a b -> Prop)
      (env1: Envr K A) (env2: Envr K B) (x:K) (a:A) (b:B):
  Forall3 R P env1 env2 -> 
  findEP env1 x a -> findEP env2 x b ->
  (forall p: R a b, P a b p). 
Proof.
  intros.
  generalize dependent p.
  dependent induction H.
  inversion H0.
  inversion H.
  intros.
  inversion H1; subst.
  inversion H3; subst.
  destruct (dEq x x0) in H5.
  inversion H5; subst.
  inversion H2; subst.
  inversion H4; subst.
  destruct (dEq x0 x0) in H7.
  inversion H7; subst.
  assert (p = p0).
  apply proof_irrelevance.
  rewrite <- H6.
  assumption.
  intuition n.
  inversion H2; subst.
  inversion H4; subst.
  destruct (dEq x x0) in H7.
  inversion H7; subst.
  intuition n.
  eapply IHForall3.
  constructor.
  assumption.
  constructor.
  assumption.
Defined.


Lemma MatchEnvsB2A {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)  
      (env1: Envr K V1) (env2: Envr K V2)
      (k: K) (v1: V1) (v2: V2):
  MatchEnvs2B R k v1 v2 env1 env2 -> MatchEnvs2 R env1 env2.
intros.
inversion H; subst.
econstructor.
eassumption.
exact H1.
exact H2.
eassumption.
reflexivity.
reflexivity.
Defined.

(*********************)


Inductive EnvPos {K V: Type} {h: DEq K} :
             Envr K V -> K -> option nat -> Prop :=
| EnvPos_Nil : forall k: K, EnvPos emptyE k None
| EnvPos_Same : forall (env: Envr K V) (k: K) (v: V),
                    EnvPos ((k,v)::env) k (Some 0)
| EnvPos_Diff : forall (env: Envr K V) (k1 k2: K)
                         (n: nat) (v: V),
                    k1 <> k2 ->
                    EnvPos env k1 (Some n) -> 
                    EnvPos ((k2,v)::env) k1 (Some (n+1)).            


Inductive EnvPrefix {K V: Type} {h: DEq K} :
             Envr K V -> K -> Envr K V -> Prop :=
| EnvPrefix_Nil : forall k: K, EnvPrefix emptyE k emptyE
| EnvPrefix_Same : forall (env: Envr K V) (k: K) (v: V),
                    EnvPrefix ((k,v)::env) k emptyE
| EnvPrefix_Diff : forall (env1 env2: Envr K V) (k1 k2: K)
                          (v: V),
                    k1 <> k2 ->
                    EnvPrefix env1 k1 env2 -> 
                    EnvPrefix ((k2,v)::env1) k1 ((k2,v)::env2).            


Inductive EnvSuffix {K V: Type} {h: DEq K} :
             Envr K V -> K -> Envr K V -> Prop :=
| EnvSuffix_Nil : forall k: K, EnvSuffix emptyE k emptyE
| EnvSuffix_Same : forall (env: Envr K V) (k: K) (v: V),
                    EnvSuffix ((k,v)::env) k env
| EnvSuffix_Diff : forall (env1 env2: Envr K V) (k1 k2: K)
                         (v: V),
                    k1 <> k2 ->
                    EnvSuffix env1 k1 env2 -> 
                    EnvSuffix ((k2,v)::env1) k1 env2.            


Lemma MatchEnvsPos {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
                    (env1: Envr K V1) (env2: Envr K V2) :
  MatchEnvs R env1 env2 ->
  forall (k: K) (n1 n2: option nat),
    EnvPos env1 k n1 ->
    EnvPos env2 k n2 ->
    n1 = n2.
Proof.
  intros.
  dependent induction H.
  inversion H0; subst.
  inversion H1; subst.
  reflexivity.
  inversion H1; subst.
  inversion H2; subst.
  reflexivity.
  intuition H8.
  inversion H2; subst.
  inversion H1; subst.
  omega.
  intuition H7.
  specialize (IHMatchEnvs k0 (Some n) (Some n0) H9 H11).
  inversion IHMatchEnvs; subst.
  reflexivity.
Defined.  


Lemma MatchEnvsPrefix {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
                    (env1: Envr K V1) (env2: Envr K V2) : 
  MatchEnvs R env1 env2 ->
  forall k env3 env4,
    EnvPrefix env1 k env3 ->
    EnvPrefix env2 k env4 ->
    MatchEnvs R env3 env4.
Proof.
  intros.
  dependent induction H.
  inversion H0; subst.
  inversion H1; subst.
  constructor.
  inversion H1; subst.
  inversion H2; subst.
  constructor.
  intuition H8.
  inversion H2; subst.
  intuition H8.
  constructor.
  assumption.
  apply (IHMatchEnvs k0).
  assumption.
  assumption.
Defined. 
  
  
Lemma MatchEnvsSuffix {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
                    (env1: Envr K V1) (env2: Envr K V2) : 
  MatchEnvs R env1 env2 ->
  forall k env3 env4,
    EnvSuffix env1 k env3 ->
    EnvSuffix env2 k env4 ->
    MatchEnvs R env3 env4.
Proof.
  intros.
  dependent induction H.
  inversion H0; subst.
  inversion H1; subst.
  constructor.
  inversion H1; subst.
  inversion H2; subst.
  assumption.
  intuition H8.
  inversion H2; subst.
  intuition H8.
  apply (IHMatchEnvs k0).
  assumption.  
  assumption.
Defined.


Lemma IsEnvPrefix {K V: Type} {h: DEq K} 
                   (env: Envr K V) (k: K) : 
  forall ls1 ls2 v,
    env = ls1 ++ ((k,v)::ls2) ->
    findE ls1 k = None ->
    EnvPrefix env k ls1.
Proof.
  intros.
  revert H H0.
  revert k v ls2 env.
  induction ls1.
  intros.
  simpl in H.
  rewrite H.
  constructor.
  intros.
  rewrite <- app_comm_cons in H.
  induction env.
  inversion H.
  inversion H; subst.
  destruct a. 
  constructor.
  inversion H0; subst.
  destruct (dEq k k0).
  inversion H2.
  assumption.
  eapply find_persists2 in H0.
  eapply IHls1 in H0.
  eassumption.
  reflexivity.
Defined.  
  

Lemma IsEnvSuffix {K V: Type} {h: DEq K} 
                   (env: Envr K V) (k: K) : 
  forall ls1 ls2 v,
    env = ls1 ++ ((k,v)::ls2) ->
    findE ls1 k = None ->
    EnvSuffix env k ls2.
Proof.
  intros.
  revert H H0.
  revert k v ls2 env.
  induction ls1.
  intros.
  simpl in H.
  rewrite H.
  constructor.
  intros.
  rewrite <- app_comm_cons in H.
  induction env.
  inversion H.
  inversion H; subst.
  destruct a. 
  constructor.
  inversion H0; subst.
  destruct (dEq k k0).
  inversion H2.
  assumption.
  eapply find_persists2 in H0.
  eapply IHls1 in H0.
  eassumption.
  reflexivity.
Defined.


Lemma IsEnvEl {K V: Type} {h: DEq K} 
                   (env: Envr K V) (k: K) : 
  forall ls1 ls2 v,
    env = ls1 ++ ((k,v)::ls2) ->
    findE ls1 k = None ->
    findEP env k v.
Proof.
  intros.
  revert H H0.
  revert k v ls2 env.
  induction ls1.
  intros.
  simpl in H.
  rewrite H.
  constructor.
  simpl.
  destruct (dEq k k).
  reflexivity.
  intuition n.
  intros.
  rewrite <- app_comm_cons in H.
  induction env.
  inversion H.
  destruct a.
  inversion H; subst.
  inversion H0; subst.
  constructor.
  simpl.
  destruct (dEq k k0).
  inversion H2.
  specialize (IHls1 k v ls2 (ls1 ++ (k, v) :: ls2) eq_refl H2).
  inversion IHls1.
  assumption.
Defined.  
  

Lemma MatchEnvsApp {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
                    (env1: Envr K V1) (env2: Envr K V2) : 
  MatchEnvs R env1 env2 ->
  forall ls1 ls2 ls3 ls4 k v1 v2,
    env1 = ls1 ++ ((k,v1)::ls3) ->
    env2 = ls2 ++ ((k,v2)::ls4) ->
    findE ls1 k = None -> 
    findE ls2 k = None -> 
    R v1 v2 /\ MatchEnvs R ls1 ls2 /\ MatchEnvs R ls3 ls4.
Proof.
  intros.
  assert (env1 = ls1 ++ (k, v1) :: ls3) as E1.
  auto.
  assert (env2 = ls2 ++ (k, v2) :: ls4) as E2.
  auto.
  eapply IsEnvPrefix in E1.
  eapply IsEnvPrefix in E2.
  intros.
  assert (env1 = ls1 ++ (k, v1) :: ls3) as F1.
  auto.
  assert (env2 = ls2 ++ (k, v2) :: ls4) as F2.
  auto.
  eapply IsEnvSuffix in F1.
  eapply IsEnvSuffix in F2.
  intros.
  assert (env1 = ls1 ++ (k, v1) :: ls3) as G1.
  auto.
  assert (env2 = ls2 ++ (k, v2) :: ls4) as G2.
  auto.
  eapply IsEnvEl in G1.
  eapply IsEnvEl in G2.
  split.
  eapply RelatedByEnvEP.
  eapply H.
  eapply G1.
  apply G2.
  split.
  eapply MatchEnvsPrefix.
  eapply H.
  eapply E1.
  apply E2.
  eapply MatchEnvsSuffix.
  eapply H.
  eapply F1.
  apply F2.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
Defined.  
  

Lemma MatchEnvsApp1 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
                    (env1: Envr K V1) (env2: Envr K V2) : 
  MatchEnvs R env1 env2 ->
  forall ls1 ls2 ls3 ls4 k v1 v2,
    env1 = ls1 ++ ((k,v1)::ls3) ->
    env2 = ls2 ++ ((k,v2)::ls4) ->
    findE ls1 k = None -> 
    findE ls2 k = None -> 
    R v1 v2.
Proof.
eapply MatchEnvsApp.
Defined.

Lemma MatchEnvsApp2 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
                    (env1: Envr K V1) (env2: Envr K V2) : 
  MatchEnvs R env1 env2 ->
  forall ls1 ls2 ls3 ls4 k v1 v2,
    env1 = ls1 ++ ((k,v1)::ls3) ->
    env2 = ls2 ++ ((k,v2)::ls4) ->
    findE ls1 k = None -> 
    findE ls2 k = None -> 
    MatchEnvs R ls1 ls2.
Proof.
eapply MatchEnvsApp.
Defined.

Lemma MatchEnvsApp3 {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)
                    (env1: Envr K V1) (env2: Envr K V2) : 
  MatchEnvs R env1 env2 ->
  forall ls1 ls2 ls3 ls4 k v1 v2,
    env1 = ls1 ++ ((k,v1)::ls3) ->
    env2 = ls2 ++ ((k,v2)::ls4) ->
    findE ls1 k = None -> 
    findE ls2 k = None -> 
    MatchEnvs R ls3 ls4.
Proof.
eapply MatchEnvsApp.
Defined.

  
Lemma MatchEnvsA2B {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)  
          (env1: Envr K V1) (env2: Envr K V2) :
  MatchEnvs2 R env1 env2 ->
  forall (k: K) (v1: V1) (v2: V2), findEP env1 k v1 ->
                                   findEP env2 k v2 -> 
                              MatchEnvs2B R k v1 v2 env1 env2.
Proof.
intros.
assert (findEP env1 k v1) as K1.
auto.
assert (findEP env2 k v2) as K2.
auto.
apply findEPtoEP2 in K1.
apply findEPtoEP2 in K2.
inversion K1.
rename H3 into K3.
inversion K2.
rename H3 into K4.
dependent induction H.
eapply (MatchEnvs2B_split R k v1 v2 nil nil nil nil nil nil).
inversion H0; subst.
inversion H.
inversion H0; subst.
inversion H.
inversion H0; subst.
inversion H.
inversion H0; subst.
inversion H.
inversion H0; subst.
inversion H.
inversion H0; subst.
inversion H.
assert (MatchEnvs R (ls1 ++ (k, v1) :: ls3) (ls2 ++ (k, v2) :: ls4)).
eapply appEnvLemma.   
assumption.
eapply consEnvLemma.
assumption.
assumption.
rewrite H3 in H7.
rewrite H4 in K4.
econstructor.
(*
inversion H5; subst.
inversion H6; subst.
*)
eapply RelatedByEnvEP.
exact H11.
rewrite <- H3.
exact H5.
rewrite <- H4.
exact H6.
(***)
instantiate (1:=m2).
instantiate (1:=m0).
(*rewrite H3 in H7.
rewrite H4 in K4.*)
eapply MatchEnvsApp2.
eapply H11.
eapply H7.
eapply K4.
assumption.
assumption.
instantiate (1:=m3).
instantiate (1:=m1).
eapply MatchEnvsApp3.
eapply H11.
eapply H7.
eapply K4.
assumption.
assumption.
assumption.
rewrite H3.
assumption.
rewrite H4.
assumption.
Defined.


Lemma forall3ConsExt {K A B :Type} {h: DEq K} (R: A -> B -> Prop)
      (P: forall (a:A) (b:B), R a b -> Prop) 
      (env1: Envr K A) (env2: Envr K B) (x:K) (a:A) (b:B) (p: R a b):
  Forall3 R P env1 env2 ->
  P a b p ->
  Forall3 R P ((x,a)::env1) ((x,b)::env2).
Proof.
  intros.
  econstructor.
  eassumption.
  assumption.  
Defined.

Lemma forall3AppExt {K A B :Type} {h: DEq K} (R: A -> B -> Prop)
      (P: forall (a:A) (b:B), R a b -> Prop) 
      (env1 env3: Envr K A) (env2 env4: Envr K B) (x:K):
  Forall3 R P env1 env2 ->
  Forall3 R P env3 env4 ->
  Forall3 R P (env1 ++ env3) (env2 ++ env4).
Proof.
  intros.
  dependent induction H.
  simpl.
  assumption.
  rewrite <- app_comm_cons.
  rewrite <- app_comm_cons. 
  econstructor.
  eassumption.
  auto.
Defined.


Lemma nilSum {A: Type} (ls1 ls2: list A) : nil = ls1 ++ ls2 ->
                                           nil = ls1 /\ nil = ls2.
 Proof.
  revert ls2.
  destruct ls1.
  intros.
  auto.
  intros.
  inversion H.
Defined.  


Lemma forall2Bto3 {K A B :Type} {h: DEq K} (R: A -> B -> Prop)
      (P: forall (a:A) (b:B), R a b -> Prop) 
      (env1: Envr K A) (env2: Envr K B) (x:K) (a:A) (b:B):
  @Forall2B K A B h R P (fun x y z => Forall3 R P x y) x a b env1 env2 ->
    Forall3 R P env1 env2.
Proof.
  intros.
  inversion H; subst.
  eapply (forall3ConsExt R P) in H3.
  instantiate (1:=b) in H3.
  instantiate (1:=x) in H3.
  instantiate (1:=a) in H3.
  eapply (forall3AppExt R P).
  auto.
  auto.
  auto.
  eauto.
Defined.
 

(*** OPEN PROBLEMS ******************8
 
Lemma forall3AppRev {K A B :Type} {h: DEq K} (R: A -> B -> Prop)
      (P: forall (a:A) (b:B), R a b -> Prop) 
      (env1 env3 envA: Envr K A) (env2 env4 envB: Envr K B)
      (x:K) (a:A) (b:B):
  findE env1 x = None ->
  findE env2 x = None ->
  envA = env1 ++ ((x,a)::env3) ->
  envB = env2 ++ ((x,b)::env4) -> 
  MatchEnvs R envA envB ->
  Forall3 R P envA envB ->
  (exists p, P a b p) /\ 
  Forall3 R P env1 env2 /\
  Forall3 R P env3 env4.
Proof.
  intros H H0 E1 E2 H1.
  revert H H0 E1 E2.
  revert env1 env3 env2 env4.
  dependent induction H1.
  intros.
  eapply nilSum in E1.
  destruct E1.
  inversion H3.
  intros.
  destruct env1.
  simpl in E1.
  inversion E1; subst.
  destruct env2.
    
 
  inversion H3; subst.
  
    
  dependent induction H2.
  eapply nilSum in E1.
  destruct E1.
  inversion H3.
  destruct env1.
  simpl in E1.
  inversion E1; subst.
  destruct env2.
  simpl in E2.
  inversion E2; subst.
  (*
  specialize (IHForall3 h nil nil nil nil x1 a b H H0).
  assert (MatchEnvs R (nil ++ (x1, a) :: nil) (nil ++ (x1, b) :: nil)).
  simpl.
  constructor.
  *)  
  split.
  eexists p.
  assumption.
  split.
  constructor.
  destruct env3.
  destruct env4.
  constructor.
  inversion H1; subst.
  inversion H10.
  destruct env4.
  inversion H1; subst.
  inversion H10.
  destruct p0.
  destruct p1.
  inversion H1; subst.
  inversion H10; subst.
  assumption.
  destruct p0.
  simpl in H1.
  inversion H1; subst.
  inversion H0; subst.
  destruct (dEq k k).
  inversion H5.
  intuition n.
  destruct p0.
  destruct env2.
  simpl in H1.
  inversion H1; subst.
  inversion H; subst.
  destruct (dEq x1 x1).
  inversion H5.
  intuition n.
  destruct p0.
  eapply IHForall3.
  eassumption.
  assumption.
  assumption.
  rewrite <- app_comm_cons in x2.
  inversion x2; subst.
  rewrite <- app_comm_cons.

  
  assert (~ (env1 ++ (x1, a) :: env3 = (k, a1) :: env1 ++ (x1, a) :: env3)).
  simplify_eq.
  induction env1.
  simpl in H4.
  inversion H4.
  inversion H8.
  intros.

  
  apply eqb_neq.
  
  unfold '~='.
  
  rewrite <- H7.

  rewrite <- app_comm_cons in x.
  inversion x.
  
    
  specialize (IHForall3 h env1 env3 env2 env4 x1 a b).
  eapply find_persists2 in H.
  eapply find_persists2 in H0.
  inversion H1; subst.
  specialize (IHForall3 H H0 H11).
  rewrite <- app_comm_cons in x2.
  inversion x2.
  rewrite <- app_comm_cons in x.
  inversion x.
  inversion H8; subst. 
  specialize IHForall3.
  
  eassumption.
  eassumption.
  assumption.
  
  
  
  split.
  inversion H1; subst.
  econstructor.
  eapply MatchEnvsApp with (ls1:=env1) (ls3:=env3) (ls2:=env2) (ls4:=env4)
                           (k:=x1) (v1:=a) (v2:=b) in H11.
  
  eapply (appEnvLemma R env1 ((x1,a)::env3) env2 ((x1,b)::env4)) in H11.
  
  destruct env3.
 
    
  eapply (IHForall3 h nil ((x1, a) :: env3) nil ((x1, b) :: env4)) in H.
  destruct H.
  inversion H3; subst.
  assumption.
  assumption.
  
  
  eapply IHForall3.
  eassumption.
  eassumption.
  
  
  split.
  constructor.
  

  
  eapply nilSum in x1.
  destruct x.
  destruct x1.
  split.
  rewrite <- H1.
  rewrite <- H.
  constructor.
  rewrite <- H2.
  rewrite <- H0.
  constructor.
  
  
  
  
  
Lemma forall3to2B {K A B :Type} {h: DEq K} (R: A -> B -> Prop)
      (P: forall (a:A) (b:B), R a b -> Prop) 
      (env1: Envr K A) (env2: Envr K B) (x:K) (a:A) (b:B):
  findEP env1 x a ->
  findEP env2 x b ->
  MatchEnvs R env1 env2 -> 
  Forall3 R P env1 env2 -> 
   @Forall2B K A B h R P (fun x y z => Forall3 R P x y) x a b env1 env2.
  intros.
(*  assert (MatchEnvs R env1 env2) as W.
  auto.
  eapply MatchEnvs1to2 in H1.
  eapply MatchEnvsA2B in H1.
  instantiate (1:=b) in H1.
  instantiate (1:=a) in H1.
  instantiate (1:=x) in H1.
  inversion H1.
  econstructor.
  exact H4.
  exact H5.
  assumption.
  assumption.
  Focus 4.
  assumption.
  Focus 4.
  assumption.
  Focus 3.
  inversion H2; subst.
*)  
  
  inversion H; subst.
  inversion H0; subst.
  dependent induction H2.
  inversion H3.
  simpl in H4.
  simpl in H5.
  destruct (dEq x x0).
  inversion H4; subst.
  inversion H5; subst.
  econstructor.
  instantiate (1:=nil).
  instantiate (1:=nil).
  constructor.
  inversion H1; subst.
  exact H12.
  reflexivity.
  reflexivity.
  constructor.
  assumption.
  exact H2.
  eapply MatchEnvs1to2 in H1.
(*  inversion H; subst. *)
(*  rewrite <- (findEextCons aas x x0 a0 n) in H6. *)
  
  eapply (MatchEnvsA2B R ((x0, a0) :: aas) ((x0, b0) :: bbs)) in H1.
  instantiate (1:=b) in H1.
  instantiate (1:=a) in H1.
  instantiate (1:=x) in H1.
  inversion H1.
  econstructor.
  exact H7.
  exact H8.  
  assumption.
  assumption.
  Focus 3.
  eassumption.
*)  


(*  
Axiom proof_irrelevance : 
  forall (P : Prop) (p q : P), p = q.
*)


Lemma prmsTypingAux1Old {A T V: Type} {h: DEq A} (R: V -> T -> Prop)
        (fps : list (A * T)) (vls : list V)
        (h2: length fps = length vls): forall n : nat,
       LiftRel R (nth_error vls n) (nth_error (map snd fps) n) ->
       (LiftRel R (nth_error 
              (map snd (zip (map fst fps) vls (map_fst_length fps vls h2))) n)
                  (nth_error (map snd fps) n)).
Proof.
  generalize h2; clear.
  dependent induction fps.
  dependent induction vls.
  intros.
  simpl.
  simpl in H.
  assumption.
  intro.
  inversion h2.
  dependent induction vls.
  intro.
  inversion h2.
  intros.
  simpl in h2.
  simpl in H.
  simpl.
  induction n.
  simpl in H.
  simpl.
  assumption. 
  simpl.
  specialize (IHfps vls (cons_length fps vls a a0 h2) n).
  simpl in H.
  specialize (IHfps H).
  assert (cons_length (map fst fps) vls (fst a) a0
                      (map_fst_length (a :: fps) (a0 :: vls) h2) = (map_fst_length fps vls (cons_length fps vls a a0 h2))).
  apply proof_irrelevance.
  rewrite H0.
  assumption.
Defined.

  
Lemma prmsTypingAux2Old {A T V: Type} {h: DEq A} (R: V -> T -> Prop)
      (fps : list (A * T)) (vls : list V) 
        (h2: length fps = length vls) (x: A): (forall n : nat,
       (LiftRel R (nth_error 
              (map snd (zip (map fst fps) vls (map_fst_length fps vls h2))) n)
                (nth_error (map snd fps) n))) ->
    (LiftRel R
    (findE (zip (map fst fps) vls (map_fst_length fps vls h2)) x)
    (findE fps x)).                                
Proof.
  generalize h2; clear.
  generalize dependent fps.
  induction vls.
  induction fps.
  intros.
  simpl.
  constructor.
  intro.
  inversion h2.
  generalize dependent vls. 
  induction fps.
  intros.
  inversion h2.
  intros.
  specialize (IHvls fps (cons_length fps vls a0 a h2)).
  assert ((forall n : nat,
           LiftRel R
             (nth_error
                (map snd
                   (zip (map fst fps) vls
                      (map_fst_length fps vls (cons_length fps vls a0 a h2))))
                n) (nth_error (map snd fps) n))).
  intro.
  simpl in H.
  assert (forall (T: Type) (b:T)
                 (ls:list T) (n: nat),
            nth_error (b::ls) (S n) = nth_error ls n).
  intros.
  clear H.
  induction ls.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  specialize (H (S n)).
  rewrite H0 in H.
  rewrite H0 in H.
  assert (cons_length (map fst fps) vls (fst a0) a
                      (map_fst_length (a0 :: fps) (a :: vls) h2) = (map_fst_length fps vls (cons_length fps vls a0 a h2))).
  apply proof_irrelevance.
  rewrite <- H1.
  assumption.  
  simpl.
  destruct a0.
  clear IHfps.
  simpl.
  destruct (dEq x a0).
  constructor.
  specialize (H 0).
  inversion H; subst.
  assumption.
  specialize (IHvls H0).
  assert (cons_length (map fst fps) vls a0 a
                      (map_fst_length ((a0,t) :: fps) (a :: vls) h2) = (map_fst_length fps vls (cons_length fps vls (a0,t) a h2))).
  apply proof_irrelevance.
  rewrite H1.
  assumption.  
Defined.  




Lemma prmsTypingAux1 {A T V: Type} (R: V -> T -> Prop)
        (fps : list (A * T)) (vls : list V)
        (h2: length fps = length vls):
  MatchLists R vls (map snd fps) ->
  MatchLists R (map snd (zip (map fst fps) vls (map_fst_length fps vls h2)))
               (map snd fps).
Proof.
  generalize h2; clear.
  dependent induction fps.
  dependent induction vls.
  intros.
  simpl.
  constructor.
  intros.  
  inversion h2.
  dependent induction vls.
  intros.
  inversion h2.  
  intros.
  simpl in h2.
  simpl in H.
  simpl.
  inversion H; subst.
  constructor.
  assumption.  
  specialize (IHfps vls (cons_length fps vls a a0 h2) H5).
  assert (cons_length (map fst fps) vls (fst a) a0
                      (map_fst_length (a :: fps) (a0 :: vls) h2) = (map_fst_length fps vls (cons_length fps vls a a0 h2))).
  apply proof_irrelevance.
  rewrite H0.
  assumption.
Defined.
 


Lemma prmsTypingAux2 {A T V: Type} {h: DEq A} (R: V -> T -> Prop)
      (fps : list (A * T)) (vls : list V) 
      (h2: length fps = length vls):

  (MatchLists R (map snd (zip (map fst fps) vls (map_fst_length fps vls h2)))
                (map snd fps)) ->
  (MatchEnvs R (zip (map fst fps) vls (map_fst_length fps vls h2)) fps).        
Proof.
  generalize h2; clear.
  generalize dependent fps.
  induction vls.
  induction fps.
  intros.
  simpl.
  constructor.
  intro.
  inversion h2.
  generalize dependent vls. 
  induction fps.
  intros.
  inversion h2.
  intros.
  specialize (IHvls fps (cons_length fps vls a0 a h2)).
  assert (MatchLists R (map snd (zip (map fst fps) vls
                      (map_fst_length fps vls (cons_length fps vls a0 a h2)))) (map snd fps)).
  simpl in H.
  inversion H; subst. 
  assert (cons_length (map fst fps) vls (fst a0) a
                      (map_fst_length (a0 :: fps) (a :: vls) h2) = (map_fst_length fps vls (cons_length fps vls a0 a h2))).
  apply proof_irrelevance.
  rewrite <- H0.
  assumption.  
  simpl.
  clear IHfps.
  destruct a0.
  simpl.
  inversion H; subst.
  constructor.
  assumption.
  specialize (IHvls H0).
  assert (cons_length (map fst fps) vls a0 a
                      (map_fst_length ((a0,t) :: fps) (a :: vls) h2) = (map_fst_length fps vls (cons_length fps vls (a0,t) a h2))).
  apply proof_irrelevance.
  rewrite H1.
  assumption.  
Defined.  



(*** Superseded *************************************************)


Inductive findEP0 {K V: Type} (m: Envr K V) (k: K) : V -> Prop :=
| FindE2 : forall x: V, In (k, x) m -> findEP0 m k x.

Inductive MatchEnvs0 {K V1 V2: Type} {h: DEq K} (rel: V1 -> V2 -> Prop) : 
          Envr K V1 -> Envr K V2 -> Prop :=
    Match_envs0 : forall (venv: Envr K V1) (tenv: Envr K V2),
          (forall (x: K), LiftRel rel 
                 (findE venv x) (findE tenv x)) ->
                MatchEnvs0 rel venv tenv.

Definition MatchEnvs2Def {K V1 V2: Type} {h: DEq K}
           (rel: V1 -> V2 -> Prop)  
           (k: K) (v1: V1) (v2: V2)
           (ls1 ls3 : Envr K V1)
           (ls2 ls4 : Envr K V2) : Prop := 
                     rel v1 v2 /\
                     MatchEnvs rel ls1 ls2 /\
                     MatchEnvs rel ls3 ls4 /\
                     findE ls2 k = None.                         


Inductive Forall2BB {K A B :Type} {h: DEq K} (R: A -> B -> Prop)
          (P: forall (a0:A) (b0:B), R a0 b0 -> Prop) :
          K -> A -> B -> Envr K A -> Envr K B -> Prop :=
| Forall2BB_one : forall (k:K) (a:A) (b:B) (p: R a b),
                 P a b p ->
                 Forall2BB R P k a b (singleE k a) (singleE k b)
| Forall2BB_cons : forall (aas as1 as2: Envr K A)
                         (bbs bs1 bs2: Envr K B) 
                         (k:K) (a:A) (b:B) (p: R a b),
                    aas = as1 ++ ((k,a)::as2) ->
                    bbs = bs1 ++ ((k,b)::bs2) ->
                    findE as1 k = None ->
                    findE bs1 k = None ->                
                    P a b p ->
                    Forall3 R P as1 bs1 ->                          
                    Forall3 R P as2 bs2 ->
                    Forall2BB R P k a b aas bbs. 


(***** Problems **)

(*
Lemma MatchEnvsA2DefEx {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)  
       (env1: Envr K V1) (env2: Envr K V2) (k: K) (v1: V1) (v2: V2) :
  MatchEnvs2 R env1 env2 ->
  findEP2 env1 k v1 ->
  findEP2 env2 k v2 -> 
  exists (env3 env5: Envr K V1) (env4 env6: Envr K V2),
    MatchEnvs2Def R k v1 v2 env3 env5 env4 env6.
  unfold MatchEnvs2Def.
  intros.
  inversion H0; subst.
  inversion H1; subst.
  exists m0.
  exists m1.
  exists m2.
  exists m3.
Admitted.
*)
(*
Lemma MatchEnvsA2Def {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)  
          (env1: Envr K V1) (env2: Envr K V2) :
  MatchEnvs2 R env1 env2 ->
  forall (env3 env5: Envr K V1) (env4 env6: Envr K V2)
         (k: K) (v1: V1) (v2: V2),
    MatchEnvs R env3 env4 ->
    env1 = overrideE env3 (updateE env5 k v1) ->
    env2 = overrideE env4 (updateE env6 k v2) -> 
    MatchEnvs2Def R k v1 v2 env3 env5 env4 env6.
Proof.
unfold MatchEnvs2Def.
intros.
split.
Admitted.  
*)

(*
Lemma MatchEnvsA2B {K V1 V2: Type} {h: DEq K} (R: V1 -> V2 -> Prop)  
          (env1: Envr K V1) (env2: Envr K V2) :
  MatchEnvs2 R env1 env2 ->
  forall (k: K) (v1: V1) (v2: V2), findEP2 env1 k v1 ->
                                   findEP2 env2 k v2 -> 
                              MatchEnvs2B R k v1 v2 env1 env2.
intros.
dependent induction H.
econstructor.
inversion H0; subst.
unfold overrideE in H.
unfold updateE in H.
apply app_cons_not_nil in H.
intuition H.
constructor.
constructor.
simpl.
reflexivity.
inversion H0.
unfold overrideE in H.
unfold updateE in H.
apply app_cons_not_nil in H.
intuition H.
inversion H0.
unfold overrideE in H.
unfold updateE in H.
apply app_cons_not_nil in H.
intuition H.
econstructor.
inversion H5; subst.
*)


(*
Lemma findEP2findE {K V: Type} {h: DEq K} (m: Envr K V) (k: K) (x: V) :
  findEP m k x -> findE m k = Some x.
  intros.
  inversion H; subst.
(*  unfold In in H0.
  unfold findE.*)
  dependent induction m.
  destruct H0.
  destruct a.
  simpl.
  destruct (dEq k k0); subst.
  inversion H0; subst.
  inversion H1; subst.
  reflexivity.
  inversion H0; subst.
  inversion H2; subst.
  reflexivity.
  simpl.
  destruct (dEq k k).
  reflexivity.
  destruct n.
  reflexivity.
  eapply IHm in H1.
  Focus 2.
  constructor.
  assumption.
*)  
  
  
(*
Definition envMap (K V1 V2: Type) (f: V1 -> V2) (g: Envr K V1) (x: K) : 
    option V2 := match g x with 
     | Some y => Some (f y)
     | None => None
     end.
*)
(*
Inductive findE (K V: Type) (m: Envr K V) (k: K) : V -> Prop :=
  | FindE : forall x: V, m k = Some x -> findE K V m k x.

Definition emptyE (K V: Type): Envr K V := fun (x: K) => None.
*)

(*
Inductive disjointH (K V1 V2: Type) (m1: Envr K V1) 
    (m2: Envr K V2) : Prop :=
   disjointH1 : (forall x:K, or (m1 x = None) (m2 x = None)) -> 
                   disjointH K V1 V2 m1 m2.
*)

(*
Inductive overrideEP (K V: Type)   
    (f1 f2 f3: Envr K V) : Prop :=
   | OverrideEP : f3 = overrideE K V f1 f2 -> overrideEP K V f1 f2 f3.
*)

(*
Definition liftH (X Y: Type) (f: env X Y) (x:option X) : option Y :=
   match x with
   | Some x1 => f x1
   | None => None
   end.
*)

(*
Lemma gtr0 (ls: list V) (n: length ls) :  > 0.
  

Fixpoint zip {V1 V2: Type} (ls1 : list V1) (ls2: list V2)
           (p: length ls1 = length ls2) : list (V1 * V2) :=
  match (length ls1) with
    | 0 => (nil, nil)
    | S n => cons (hd_total ls1 (gtr0 (S n)), hd_total ls2 (gtr0 (S n)))   
               (zip (tl ls1) (tl ls2) (tl_length ls1 ls2 p))
    end.
*)

