Require Export Basics.
Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Export EnvListAux7.
Require Export EnvListAuxT1.
Require Export TPipStaticM2.

Module StaticInduct (IdT: IdModType) <: IdModType.

Module StaticC := Static IdT.
Export StaticC.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.


Lemma ExpTyping_gen_str_rect : forall 

(* properties *)
                        
         (PPF : forall (f : Fun) (ft : FTyp),
                  FunTyping f ft -> Type)
         
         (PPQ : forall (ftenv : funTC) (fenv : funEnv)
                       (q : QFun) (ft : FTyp),
                  QFunTyping ftenv fenv q ft -> Type)
         
         (PPE : forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
                       (e : Exp) (v : VTyp),
                  ExpTyping ftenv tenv fenv e v -> Type)
         
         (PPP : forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
                       (ps : Prms) (pt : PTyp),
                  PrmsTyping ftenv tenv fenv ps pt -> Type)
         
         (SSL : forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv)
                       (es: list Exp) (ts: list VTyp), 
		  Forall2T (ExpTyping ftenv tenv fenv) es ts -> Type)

         (SSA : forall (ftenv : funTC) (fenv: funEnv), 
		  MatchEnvsT FunTyping fenv ftenv -> Type)
         
         (SSB : forall (ftenv : funTC) (fenv: funEnv)
                       (x:Id) (f: Fun) (ft:FTyp), 
		  MatchEnvs2BT FunTyping x f ft fenv ftenv -> Type), 
                        
(** SSL cases **)
       
       (forall (ftenv : funTC) (tenv : valTC) (fenv: funEnv),
        SSL ftenv tenv fenv nil nil 
           (Forall2_nilT (ExpTyping ftenv tenv fenv))) ->

         
       (forall (ftenv : funTC) (tenv : valTC) (fenv: funEnv) 
               (es : list Exp) (ts : list VTyp)
               (e: Exp) (t: VTyp)
               (m1: ExpTyping ftenv tenv fenv e t)               
               (m2 : Forall2T (ExpTyping ftenv tenv fenv) es ts),
        SSL ftenv tenv fenv es ts m2 -> 
	PPE ftenv tenv fenv e t m1 ->  
	SSL ftenv tenv fenv (e::es) (t::ts)
         (Forall2_consT (ExpTyping ftenv tenv fenv) e t es ts m1 m2)) ->

(** SSA cases **)

       (SSA nil nil (MatchEnvs_NilT FunTyping)) ->

       
       (forall (ftenv : funTC) (fenv : funEnv)
               (x:Id) (f: Fun) (t: FTyp)
               (m1: FunTyping f t)
               (m2 : MatchEnvsT FunTyping fenv ftenv),
        SSA ftenv fenv m2 -> 
	PPF f t m1 ->  
        SSA ((x,t)::ftenv) ((x,f)::fenv)
            (MatchEnvs_ConsT FunTyping fenv ftenv x f t m1 m2)) ->

(** SSB cases **)

       (forall (ftenv ftenv0 ftenv1: funTC)
               (fenv fenv0 fenv1: funEnv)
               (x:Id) (f: Fun) (t: FTyp)
               (k: FunTyping f t)
               (m0 : MatchEnvsT FunTyping fenv0 ftenv0)
               (m1 : MatchEnvsT FunTyping fenv1 ftenv1)
               (h1 : findE ftenv0 x = None)
               (h2 : fenv = fenv0 ++ ((x,f)::fenv1))
               (h3 : ftenv = ftenv0 ++ ((x,t)::ftenv1)),                  
        SSA ftenv0 fenv0 m0 -> 
        SSA ftenv1 fenv1 m1 ->                                       
        PPF f t k -> 
        SSB ftenv fenv x f t
           (MatchEnvs2B_splitT FunTyping x f t 
               fenv ftenv fenv0 ftenv0 fenv1 ftenv1 k m0 m1 h1 h2 h3)) ->
         
(** PPF cases *)
      
(* FunZ *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
          (e0 e1 : Exp) (x : Id) (t : VTyp)
          (m : MatchEnvsT FunTyping fenv ftenv)
          (k : ExpTyping ftenv tenv fenv e0 t),
        PPE ftenv tenv fenv e0 t k ->
        PPF (FC fenv tenv e0 e1 x 0) (FT tenv t)
            (FunZ_Typing ftenv tenv fenv e0 e1 x t m k)) ->

(* FunS *)       
       (forall (ftenv ftenv' : funTC) (tenv : valTC) 
               (fenv fenv' : funEnv)
               (e0 e1 : Exp) (x : Id) 
               (n : nat) (t : VTyp)
               (h1 : ftenv' = updateE ftenv x (FT tenv t))
               (h2 : fenv' = updateE fenv x (FC fenv tenv e0 e1 x n))
               (m : MatchEnvsT FunTyping fenv ftenv)
               (k1 : ExpTyping ftenv' tenv fenv' e1 t)
               (k2 : FunTyping (FC fenv tenv e0 e1 x n) (FT tenv t)),
        PPE ftenv' tenv fenv' e1 t k1 ->
        PPF (FC fenv tenv e0 e1 x n) (FT tenv t) k2 ->
        PPF (FC fenv tenv e0 e1 x (S n)) (FT tenv t)
                (FunS_Typing ftenv ftenv' tenv fenv fenv'
                                      e0 e1 x n t h1 h2 m k1 k2)) ->
       
(** PPQ cases *)
       
(* QF *)       
       (forall (ftenv : funTC) (fenv : funEnv)
               (f : Fun) (ft : FTyp)
               (k : FunTyping f ft),
        PPF f ft k ->
        PPQ ftenv fenv (QF f) ft (QF_Typing ftenv fenv f ft k)) ->

(* FVar  *)       
       (forall (ftenv : funTC) (fenv : funEnv) (x : Id) 
               (f : Fun) (ft : FTyp)
               (m : MatchEnvs2BT FunTyping x f ft fenv ftenv),
        SSB ftenv fenv x f ft m ->     
        PPQ ftenv fenv (FVar x) ft (FVar_Typing ftenv fenv x f ft m)) ->

(** PPE cases *)
       
(* Modify *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv)
               (T1 T2 : Type) (VT1 : ValTyp T1) (VT2 : ValTyp T2)
               (XF: XFun T1 T2) (q : QValue)
               (k : QValueTyping tenv q (vtyp T1)),
          PPE ftenv tenv fenv (Modify T1 T2 VT1 VT2 XF q) (vtyp T2)
              (Modify_Typing ftenv tenv fenv T1 T2 VT1 VT2 XF q k)) ->

(* Return *)
       (forall (G : Tag)
               (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
               (q : QValue) (t : VTyp)
               (k : QValueTyping tenv q t),
        PPE ftenv tenv fenv (Return G q) t
            (Return_Typing G ftenv tenv fenv q t k)) ->

(* BindN *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
               (e1 e2 : Exp) (t1 t2 : VTyp)
               (k1 : ExpTyping ftenv tenv fenv e1 t1)
               (k2 : ExpTyping ftenv tenv fenv e2 t2),
        PPE ftenv tenv fenv e1 t1 k1 ->
        PPE ftenv tenv fenv e2 t2 k2 ->
        PPE ftenv tenv fenv (BindN e1 e2) t2
            (BindN_Typing ftenv tenv fenv e1 e2 t1 t2 k1 k2)) ->
       
(* BindS *)       
       (forall (ftenv : funTC) (tenv tenv' : valTC) 
               (fenv : funEnv) (x : Id) (e1 e2 : Exp) (t1 t2 : VTyp)
               (h : tenv' = updateE tenv x t1)
               (k1 : ExpTyping ftenv tenv fenv e1 t1) 
               (k2 : ExpTyping ftenv tenv' fenv e2 t2),
        PPE ftenv tenv fenv e1 t1 k1 ->
        PPE ftenv tenv' fenv e2 t2 k2 ->
        PPE ftenv tenv fenv (BindS x e1 e2) t2
            (BindS_Typing ftenv tenv tenv' fenv x e1 e2 t1 t2 h k1 k2)) ->

(* BindMS *)       
       (forall (ftenv ftenvP ftenv' : funTC) (tenv tenvP tenv' : valTC)
               (fenv fenvP fenv' : funEnv) (envP : valEnv) 
               (e : Exp) (t : VTyp)
               (k1 : EnvTyping envP tenvP)
               (m1 : MatchEnvsT FunTyping fenv ftenv)
               (m2 : MatchEnvsT FunTyping fenvP ftenvP)
               (h1: tenv' = overrideE tenvP tenv)
               (h2: ftenv' = overrideE ftenvP ftenv)
               (h3: fenv' = overrideE fenvP fenv)
               (k2: ExpTyping ftenv' tenv' fenv' e t),
        PPE ftenv' tenv' fenv' e t k2 ->
        PPE ftenv tenv fenv (BindMS fenvP envP e) t
          (BindMS_Typing ftenv ftenvP ftenv' tenv tenvP tenv' fenv fenvP
             fenv' envP e t k1 m1 m2 h1 h2 h3 k2)) ->

(* Apply *)
       (forall (ftenv : funTC) (tenv fps : valTC) (fenv : funEnv)
               (q : QFun) (ps : Prms) (pt : PTyp) (t : VTyp)
               (h : pt = env2ptyp fps)
               (m : MatchEnvsT FunTyping fenv ftenv)
               (k1 : QFunTyping ftenv fenv q (FT fps t))
               (k2 : PrmsTyping ftenv tenv fenv ps pt),
        PPQ ftenv fenv q (FT fps t) k1 ->
        PPP ftenv tenv fenv ps pt k2 ->
        PPE ftenv tenv fenv (Apply q ps) t
            (Apply_Typing ftenv tenv fps fenv q ps pt t h m k1 k2)) ->

(* Val *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
               (v : Value) (t : VTyp)
               (k : ValueTyping v t),
          PPE ftenv tenv fenv (Val v) t
              (Val_Typing ftenv tenv fenv v t k)) ->

(* IfThenElse *)
       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv)
          (e1 e2 e3 : Exp) (t : VTyp)
          (k1 : ExpTyping ftenv tenv fenv e1 Bool)
          (k2 : ExpTyping ftenv tenv fenv e2 t)
          (k3 : ExpTyping ftenv tenv fenv e3 t),
        PPE ftenv tenv fenv e1 Bool k1 ->
        PPE ftenv tenv fenv e2 t k2 ->
        PPE ftenv tenv fenv e3 t k3 ->
        PPE ftenv tenv fenv (IfThenElse e1 e2 e3) t
           (IfThenElse_Typing ftenv tenv fenv e1 e2 e3 t k1 k2 k3)) ->

(** PPQ cases *)
       
(* PS *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
               (es : list Exp) (ts : list VTyp)
               (m : Forall2T (ExpTyping ftenv tenv fenv) es ts),
        SSL ftenv tenv fenv es ts m ->   
        PPP ftenv tenv fenv (PS es) (PT ts)
            (PS_Typing ftenv tenv fenv es ts m)) ->

(** PPE conclusion *)
       
       forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
              (e : Exp) (v : VTyp)
              (k : ExpTyping ftenv tenv fenv e v),
        PPE ftenv tenv fenv e v k.

Proof.
  intros PPF PPQ PPE PPP SSL SSA SSB.
  intros.
  revert ftenv tenv fenv e v k.
  
  fix HP_E 6 with
  (HP_F (f : Fun) (ft : FTyp) (k: FunTyping f ft) {struct k}:
                                           PPF f ft k)
  (HP_Q (ftenv : funTC) (fenv: funEnv) (h : QFun) (ft : FTyp)                           (k: QFunTyping ftenv fenv h ft) {struct k}:
                                           PPQ ftenv fenv h ft k)
  (HP_P (ftenv : funTC) (tenv : valTC) (fenv: funEnv) (ps : Prms) (ts : PTyp) 
       (k: PrmsTyping ftenv tenv fenv ps ts) {struct k}: 
                                           PPP ftenv tenv fenv ps ts k).

(* PPE *)  
- intros.
  destruct k.
  + apply X8.
  + apply X9.
  + apply X10.
    * apply HP_E.
    * apply HP_E.
  + apply X11.
    * apply HP_E.
    * apply HP_E.
  + apply X12.
    * apply HP_E.
  + apply X13.
    * apply HP_Q.
    * apply HP_P.
  + apply X14.
  + apply X15.
    * apply HP_E.
    * apply HP_E.
    * apply HP_E.
(* PPF *)
- intros.
  destruct k.
  + apply X4.
    apply HP_E.
  + apply X5.
    apply HP_E.
    apply HP_F.
(* PPQ *)    
- intros.
  destruct k.
  + apply X6.
    apply HP_F.
  + apply X7.
    destruct m.
    * apply X3.
      {- revert m e e0 e1.
         revert ls2 ls1 ls5 ls6.
         fix HP_QA 5.
         intros.
         destruct m.
         + apply X1.
         + apply X2.
           * apply HP_QA with (ls5:=ls1 ++ (x, f) :: ls3)
                              (ls6:=ls2 ++ (x, ft) :: ls4).
             {- inversion e; subst.
                destruct (IdT.IdEqDec x k).
                + inversion H0.
                + reflexivity.
             }
             {- reflexivity. }
             {- reflexivity. }
           * apply HP_F.
      }       
      {- revert m0 e e0 e1.
         revert ls4 ls3 ls5 ls6.
         fix HP_QA 5.
         intros.
         destruct m0.
         + apply X1. 
         + apply X2.
           * apply HP_QA with (ls5:=ls1 ++ (x, f) :: ls0)
                                (ls6:=ls2 ++ (x, ft) :: ls3).
             {- assumption. }
             {- reflexivity. }
             {- reflexivity. }
           * apply HP_F.
      }      
      {- apply HP_F. }
(* PPP *)      
- intros.
  destruct k.
  apply X16.
  revert f.
  revert es ts.
  fix HP_QL 3.
  intros.
  destruct f.
  + apply X.
  + apply X0.
    * apply HP_QL.
    * apply HP_E.
Defined.      
 
(*********************************************************************)


Definition Par_SSL 
  (PE : forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
                       (e : Exp) (v : VTyp),
                  ExpTyping ftenv tenv fenv e v -> Type) :=
  fun (ftenv : funTC) (tenv : valTC) (fenv: funEnv)
      (es: list Exp) (ts: list VTyp) 
      (m:  Forall2T (ExpTyping ftenv tenv fenv) es ts) =>
   Forall3AT (ExpTyping ftenv tenv fenv) 
             (fun (e: Exp) (t: VTyp) (k: ExpTyping ftenv tenv fenv e t) =>
                 PE ftenv tenv fenv e t k)
             es ts.      

Definition Par_SSA 
  (PF : forall (f : Fun) (ft : FTyp), FunTyping f ft -> Type) :=
  fun (ftenv : funTC) (fenv: funEnv)
      (m: MatchEnvsT FunTyping fenv ftenv) =>
   Forall3T FunTyping
            (fun (f: Fun) (ft: FTyp) (k: FunTyping f ft) => PF f ft k)
            fenv ftenv.      

Definition Par_SSB 
           (PF : forall (f : Fun) (ft : FTyp), FunTyping f ft -> Type) :=
  fun (ftenv : funTC) (fenv: funEnv) (x: Id) (f: Fun) (ft: FTyp)               
      (mb: MatchEnvs2BT FunTyping x f ft fenv ftenv) =>
        @Forall2BT Id Fun FTyp IdEq FunTyping PF  
                   (fun (fenv: funEnv) (ftenv : funTC)
                        (ma: MatchEnvsT FunTyping fenv ftenv) =>
                      Par_SSA PF ftenv fenv ma)
                   x f ft fenv ftenv.      


Definition ExpTyping_str_rect PPF PPQ PPE PPP :=
  ExpTyping_gen_str_rect PPF PPQ PPE PPP
       (Par_SSL PPE) (Par_SSA PPF) (Par_SSB PPF).
   
    
(***********************************************************************)


Lemma ExpTypingF_gen_str_rect : forall 

(* properties *)
                        
         (PPF : forall (f : Fun) (ft : FTyp),
                  FunTyping f ft -> Type)
         
         (PPQ : forall (ftenv : funTC) (fenv : funEnv)
                       (q : QFun) (ft : FTyp),
                  QFunTyping ftenv fenv q ft -> Type)
         
         (PPE : forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
                       (e : Exp) (v : VTyp),
                  ExpTyping ftenv tenv fenv e v -> Type)
         
         (PPP : forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
                       (ps : Prms) (pt : PTyp),
                  PrmsTyping ftenv tenv fenv ps pt -> Type)
         
         (SSL : forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv)
                       (es: list Exp) (ts: list VTyp), 
		  Forall2T (ExpTyping ftenv tenv fenv) es ts -> Type)

         (SSA : forall (ftenv : funTC) (fenv: funEnv), 
		  MatchEnvsT FunTyping fenv ftenv -> Type)
         
         (SSB : forall (ftenv : funTC) (fenv: funEnv)
                       (x:Id) (f: Fun) (ft:FTyp), 
		  MatchEnvs2BT FunTyping x f ft fenv ftenv -> Type), 
                        
(** SSL cases **)
       
       (forall (ftenv : funTC) (tenv : valTC) (fenv: funEnv),
        SSL ftenv tenv fenv nil nil 
           (Forall2_nilT (ExpTyping ftenv tenv fenv))) ->

         
       (forall (ftenv : funTC) (tenv : valTC) (fenv: funEnv) 
               (es : list Exp) (ts : list VTyp)
               (e: Exp) (t: VTyp)
               (m1: ExpTyping ftenv tenv fenv e t)               
               (m2 : Forall2T (ExpTyping ftenv tenv fenv) es ts),
        SSL ftenv tenv fenv es ts m2 -> 
	PPE ftenv tenv fenv e t m1 ->  
	SSL ftenv tenv fenv (e::es) (t::ts)
         (Forall2_consT (ExpTyping ftenv tenv fenv) e t es ts m1 m2)) ->

(** SSA cases **)

       (SSA nil nil (MatchEnvs_NilT FunTyping)) ->

       
       (forall (ftenv : funTC) (fenv : funEnv)
               (x:Id) (f: Fun) (t: FTyp)
               (m1: FunTyping f t)
               (m2 : MatchEnvsT FunTyping fenv ftenv),
        SSA ftenv fenv m2 -> 
	PPF f t m1 ->  
        SSA ((x,t)::ftenv) ((x,f)::fenv)
            (MatchEnvs_ConsT FunTyping fenv ftenv x f t m1 m2)) ->

(** SSB cases **)

       (forall (ftenv ftenv0 ftenv1: funTC)
               (fenv fenv0 fenv1: funEnv)
               (x:Id) (f: Fun) (t: FTyp)
               (k: FunTyping f t)
               (m0 : MatchEnvsT FunTyping fenv0 ftenv0)
               (m1 : MatchEnvsT FunTyping fenv1 ftenv1)
               (h1 : findE ftenv0 x = None)
               (h2 : fenv = fenv0 ++ ((x,f)::fenv1))
               (h3 : ftenv = ftenv0 ++ ((x,t)::ftenv1)),                  
        SSA ftenv0 fenv0 m0 -> 
        SSA ftenv1 fenv1 m1 ->                                       
        PPF f t k -> 
        SSB ftenv fenv x f t
           (MatchEnvs2B_splitT FunTyping x f t 
               fenv ftenv fenv0 ftenv0 fenv1 ftenv1 k m0 m1 h1 h2 h3)) ->
         
(** PPF cases *)
      
(* FunZ *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
          (e0 e1 : Exp) (x : Id) (t : VTyp)
          (m : MatchEnvsT FunTyping fenv ftenv)
          (k : ExpTyping ftenv tenv fenv e0 t),
        PPE ftenv tenv fenv e0 t k ->
        PPF (FC fenv tenv e0 e1 x 0) (FT tenv t)
            (FunZ_Typing ftenv tenv fenv e0 e1 x t m k)) ->

(* FunS *)       
       (forall (ftenv ftenv' : funTC) (tenv : valTC) 
               (fenv fenv' : funEnv)
               (e0 e1 : Exp) (x : Id) 
               (n : nat) (t : VTyp)
               (h1 : ftenv' = updateE ftenv x (FT tenv t))
               (h2 : fenv' = updateE fenv x (FC fenv tenv e0 e1 x n))
               (m : MatchEnvsT FunTyping fenv ftenv)
               (k1 : ExpTyping ftenv' tenv fenv' e1 t)
               (k2 : FunTyping (FC fenv tenv e0 e1 x n) (FT tenv t)),
        PPE ftenv' tenv fenv' e1 t k1 ->
        PPF (FC fenv tenv e0 e1 x n) (FT tenv t) k2 ->
        PPF (FC fenv tenv e0 e1 x (S n)) (FT tenv t)
                (FunS_Typing ftenv ftenv' tenv fenv fenv'
                                      e0 e1 x n t h1 h2 m k1 k2)) ->
       
(** PPQ cases *)
       
(* QF *)       
       (forall (ftenv : funTC) (fenv : funEnv)
               (f : Fun) (ft : FTyp)
               (k : FunTyping f ft),
        PPF f ft k ->
        PPQ ftenv fenv (QF f) ft (QF_Typing ftenv fenv f ft k)) ->

(* FVar  *)       
       (forall (ftenv : funTC) (fenv : funEnv) (x : Id) 
               (f : Fun) (ft : FTyp)
               (m : MatchEnvs2BT FunTyping x f ft fenv ftenv),
        SSB ftenv fenv x f ft m ->     
        PPQ ftenv fenv (FVar x) ft (FVar_Typing ftenv fenv x f ft m)) ->

(** PPE cases *)
       
(* Modify *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv)
               (T1 T2 : Type) (VT1 : ValTyp T1) (VT2 : ValTyp T2)
               (XF: XFun T1 T2) (q : QValue)
               (k : QValueTyping tenv q (vtyp T1)),
          PPE ftenv tenv fenv (Modify T1 T2 VT1 VT2 XF q) (vtyp T2)
              (Modify_Typing ftenv tenv fenv T1 T2 VT1 VT2 XF q k)) ->

(* Return *)
       (forall (G : Tag)
               (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
               (q : QValue) (t : VTyp)
               (k : QValueTyping tenv q t),
        PPE ftenv tenv fenv (Return G q) t
            (Return_Typing G ftenv tenv fenv q t k)) ->

(* BindN *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
               (e1 e2 : Exp) (t1 t2 : VTyp)
               (k1 : ExpTyping ftenv tenv fenv e1 t1)
               (k2 : ExpTyping ftenv tenv fenv e2 t2),
        PPE ftenv tenv fenv e1 t1 k1 ->
        PPE ftenv tenv fenv e2 t2 k2 ->
        PPE ftenv tenv fenv (BindN e1 e2) t2
            (BindN_Typing ftenv tenv fenv e1 e2 t1 t2 k1 k2)) ->
       
(* BindS *)       
       (forall (ftenv : funTC) (tenv tenv' : valTC) 
               (fenv : funEnv) (x : Id) (e1 e2 : Exp) (t1 t2 : VTyp)
               (h : tenv' = updateE tenv x t1)
               (k1 : ExpTyping ftenv tenv fenv e1 t1) 
               (k2 : ExpTyping ftenv tenv' fenv e2 t2),
        PPE ftenv tenv fenv e1 t1 k1 ->
        PPE ftenv tenv' fenv e2 t2 k2 ->
        PPE ftenv tenv fenv (BindS x e1 e2) t2
            (BindS_Typing ftenv tenv tenv' fenv x e1 e2 t1 t2 h k1 k2)) ->

(* BindMS *)       
       (forall (ftenv ftenvP ftenv' : funTC) (tenv tenvP tenv' : valTC)
               (fenv fenvP fenv' : funEnv) (envP : valEnv) 
               (e : Exp) (t : VTyp)
               (k1 : EnvTyping envP tenvP)
               (m1 : MatchEnvsT FunTyping fenv ftenv)
               (m2 : MatchEnvsT FunTyping fenvP ftenvP)
               (h1: tenv' = overrideE tenvP tenv)
               (h2: ftenv' = overrideE ftenvP ftenv)
               (h3: fenv' = overrideE fenvP fenv)
               (k2: ExpTyping ftenv' tenv' fenv' e t),
        PPE ftenv' tenv' fenv' e t k2 ->
        PPE ftenv tenv fenv (BindMS fenvP envP e) t
          (BindMS_Typing ftenv ftenvP ftenv' tenv tenvP tenv' fenv fenvP
             fenv' envP e t k1 m1 m2 h1 h2 h3 k2)) ->

(* Apply *)
       (forall (ftenv : funTC) (tenv fps : valTC) (fenv : funEnv)
               (q : QFun) (ps : Prms) (pt : PTyp) (t : VTyp)
               (h : pt = env2ptyp fps)
               (m : MatchEnvsT FunTyping fenv ftenv)
               (k1 : QFunTyping ftenv fenv q (FT fps t))
               (k2 : PrmsTyping ftenv tenv fenv ps pt),
        PPQ ftenv fenv q (FT fps t) k1 ->
        PPP ftenv tenv fenv ps pt k2 ->
        PPE ftenv tenv fenv (Apply q ps) t
            (Apply_Typing ftenv tenv fps fenv q ps pt t h m k1 k2)) ->

(* Val *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
               (v : Value) (t : VTyp)
               (k : ValueTyping v t),
          PPE ftenv tenv fenv (Val v) t
              (Val_Typing ftenv tenv fenv v t k)) ->

(* IfThenElse *)
       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv)
          (e1 e2 e3 : Exp) (t : VTyp)
          (k1 : ExpTyping ftenv tenv fenv e1 Bool)
          (k2 : ExpTyping ftenv tenv fenv e2 t)
          (k3 : ExpTyping ftenv tenv fenv e3 t),
        PPE ftenv tenv fenv e1 Bool k1 ->
        PPE ftenv tenv fenv e2 t k2 ->
        PPE ftenv tenv fenv e3 t k3 ->
        PPE ftenv tenv fenv (IfThenElse e1 e2 e3) t
           (IfThenElse_Typing ftenv tenv fenv e1 e2 e3 t k1 k2 k3)) ->

(** PPQ cases *)
       
(* PS *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
               (es : list Exp) (ts : list VTyp)
               (m : Forall2T (ExpTyping ftenv tenv fenv) es ts),
        SSL ftenv tenv fenv es ts m ->   
        PPP ftenv tenv fenv (PS es) (PT ts)
            (PS_Typing ftenv tenv fenv es ts m)) ->


(** PPF conclusion *)

       forall (f : Fun) (ft : FTyp) 
              (k: FunTyping f ft), 
        PPF f ft k.

Proof.
  intros PPF PPQ PPE PPP SSL SSA SSB.
  intros.
  revert f ft k.
  
  fix HP_F 3 with

  (HP_E (ftenv : funTC) (tenv : valTC) (fenv : funEnv) (e : Exp)
        (v : VTyp) (k: ExpTyping ftenv tenv fenv e v) {struct k}:
                                           PPE ftenv tenv fenv e v k) 
  (HP_Q (ftenv : funTC) (fenv: funEnv) (h : QFun) (ft : FTyp)                           (k: QFunTyping ftenv fenv h ft) {struct k}:
                                           PPQ ftenv fenv h ft k)
  (HP_P (ftenv : funTC) (tenv : valTC) (fenv: funEnv) (ps : Prms) (ts : PTyp) 
       (k: PrmsTyping ftenv tenv fenv ps ts) {struct k}: 
                                           PPP ftenv tenv fenv ps ts k).

(* PPF *)
- intros.
  destruct k.
  + apply X4.
    apply HP_E.
  + apply X5.
    apply HP_E.
    apply HP_F.
(* PPE *)  
- intros.
  destruct k.
  + apply X8.
  + apply X9.
  + apply X10.
    * apply HP_E.
    * apply HP_E.
  + apply X11.
    * apply HP_E.
    * apply HP_E.
  + apply X12.
    * apply HP_E.
  + apply X13.
    * apply HP_Q.
    * apply HP_P.
  + apply X14.
  + apply X15.
    * apply HP_E.
    * apply HP_E.
    * apply HP_E.
(* PPQ *)    
- intros.
  destruct k.
  + apply X6.
    apply HP_F.
  + apply X7.
    destruct m.
    * apply X3.
      {- revert m e e0 e1.
         revert ls2 ls1 ls5 ls6.
         fix HP_QA 5.
         intros.
         destruct m.
         + apply X1.
         + apply X2.
           * apply HP_QA with (ls5:=ls1 ++ (x, f) :: ls3)
                              (ls6:=ls2 ++ (x, ft) :: ls4).
             {- inversion e; subst.
                destruct (IdT.IdEqDec x k).
                + inversion H0.
                + reflexivity.
             }
             {- reflexivity. }
             {- reflexivity. }
           * apply HP_F.
      }       
      {- revert m0 e e0 e1.
         revert ls4 ls3 ls5 ls6.
         fix HP_QA 5.
         intros.
         destruct m0.
         + apply X1. 
         + apply X2.
           * apply HP_QA with (ls5:=ls1 ++ (x, f) :: ls0)
                                (ls6:=ls2 ++ (x, ft) :: ls3).
             {- assumption. }
             {- reflexivity. }
             {- reflexivity. }
           * apply HP_F.
      }      
      {- apply HP_F. }
(* PPP *)      
- intros.
  destruct k.
  apply X16.
  revert f.
  revert es ts.
  fix HP_QL 3.
  intros.
  destruct f.
  + apply X.
  + apply X0.
    * apply HP_QL.
    * apply HP_E.
Defined.      


Definition ExpTypingF_str_rect PPF PPQ PPE PPP :=
  ExpTypingF_gen_str_rect PPF PPQ PPE PPP
       (Par_SSL PPE) (Par_SSA PPF) (Par_SSB PPF).
   



(***********************************************************************)


Lemma ExpTypingP_gen_str_rect : forall 

(* properties *)
                        
         (PPF : forall (f : Fun) (ft : FTyp),
                  FunTyping f ft -> Type)
         
         (PPQ : forall (ftenv : funTC) (fenv : funEnv)
                       (q : QFun) (ft : FTyp),
                  QFunTyping ftenv fenv q ft -> Type)
         
         (PPE : forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
                       (e : Exp) (v : VTyp),
                  ExpTyping ftenv tenv fenv e v -> Type)
         
         (PPP : forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
                       (ps : Prms) (pt : PTyp),
                  PrmsTyping ftenv tenv fenv ps pt -> Type)
         
         (SSL : forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv)
                       (es: list Exp) (ts: list VTyp), 
		  Forall2T (ExpTyping ftenv tenv fenv) es ts -> Type)

         (SSA : forall (ftenv : funTC) (fenv: funEnv), 
		  MatchEnvsT FunTyping fenv ftenv -> Type)
         
         (SSB : forall (ftenv : funTC) (fenv: funEnv)
                       (x:Id) (f: Fun) (ft:FTyp), 
		  MatchEnvs2BT FunTyping x f ft fenv ftenv -> Type), 
                        
(** SSL cases **)
       
       (forall (ftenv : funTC) (tenv : valTC) (fenv: funEnv),
        SSL ftenv tenv fenv nil nil 
           (Forall2_nilT (ExpTyping ftenv tenv fenv))) ->

         
       (forall (ftenv : funTC) (tenv : valTC) (fenv: funEnv) 
               (es : list Exp) (ts : list VTyp)
               (e: Exp) (t: VTyp)
               (m1: ExpTyping ftenv tenv fenv e t)               
               (m2 : Forall2T (ExpTyping ftenv tenv fenv) es ts),
        SSL ftenv tenv fenv es ts m2 -> 
	PPE ftenv tenv fenv e t m1 ->  
	SSL ftenv tenv fenv (e::es) (t::ts)
         (Forall2_consT (ExpTyping ftenv tenv fenv) e t es ts m1 m2)) ->

(** SSA cases **)

       (SSA nil nil (MatchEnvs_NilT FunTyping)) ->

       
       (forall (ftenv : funTC) (fenv : funEnv)
               (x:Id) (f: Fun) (t: FTyp)
               (m1: FunTyping f t)
               (m2 : MatchEnvsT FunTyping fenv ftenv),
        SSA ftenv fenv m2 -> 
	PPF f t m1 ->  
        SSA ((x,t)::ftenv) ((x,f)::fenv)
            (MatchEnvs_ConsT FunTyping fenv ftenv x f t m1 m2)) ->

(** SSB cases **)

       (forall (ftenv ftenv0 ftenv1: funTC)
               (fenv fenv0 fenv1: funEnv)
               (x:Id) (f: Fun) (t: FTyp)
               (k: FunTyping f t)
               (m0 : MatchEnvsT FunTyping fenv0 ftenv0)
               (m1 : MatchEnvsT FunTyping fenv1 ftenv1)
               (h1 : findE ftenv0 x = None)
               (h2 : fenv = fenv0 ++ ((x,f)::fenv1))
               (h3 : ftenv = ftenv0 ++ ((x,t)::ftenv1)),                  
        SSA ftenv0 fenv0 m0 -> 
        SSA ftenv1 fenv1 m1 ->                                       
        PPF f t k -> 
        SSB ftenv fenv x f t
           (MatchEnvs2B_splitT FunTyping x f t 
               fenv ftenv fenv0 ftenv0 fenv1 ftenv1 k m0 m1 h1 h2 h3)) ->
         
(** PPF cases *)
      
(* FunZ *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
          (e0 e1 : Exp) (x : Id) (t : VTyp)
          (m : MatchEnvsT FunTyping fenv ftenv)
          (k : ExpTyping ftenv tenv fenv e0 t),
        PPE ftenv tenv fenv e0 t k ->
        PPF (FC fenv tenv e0 e1 x 0) (FT tenv t)
            (FunZ_Typing ftenv tenv fenv e0 e1 x t m k)) ->

(* FunS *)       
       (forall (ftenv ftenv' : funTC) (tenv : valTC) 
               (fenv fenv' : funEnv)
               (e0 e1 : Exp) (x : Id) 
               (n : nat) (t : VTyp)
               (h1 : ftenv' = updateE ftenv x (FT tenv t))
               (h2 : fenv' = updateE fenv x (FC fenv tenv e0 e1 x n))
               (m : MatchEnvsT FunTyping fenv ftenv)
               (k1 : ExpTyping ftenv' tenv fenv' e1 t)
               (k2 : FunTyping (FC fenv tenv e0 e1 x n) (FT tenv t)),
        PPE ftenv' tenv fenv' e1 t k1 ->
        PPF (FC fenv tenv e0 e1 x n) (FT tenv t) k2 ->
        PPF (FC fenv tenv e0 e1 x (S n)) (FT tenv t)
                (FunS_Typing ftenv ftenv' tenv fenv fenv'
                                      e0 e1 x n t h1 h2 m k1 k2)) ->
       
(** PPQ cases *)
       
(* QF *)       
       (forall (ftenv : funTC) (fenv : funEnv)
               (f : Fun) (ft : FTyp)
               (k : FunTyping f ft),
        PPF f ft k ->
        PPQ ftenv fenv (QF f) ft (QF_Typing ftenv fenv f ft k)) ->

(* FVar  *)       
       (forall (ftenv : funTC) (fenv : funEnv) (x : Id) 
               (f : Fun) (ft : FTyp)
               (m : MatchEnvs2BT FunTyping x f ft fenv ftenv),
        SSB ftenv fenv x f ft m ->     
        PPQ ftenv fenv (FVar x) ft (FVar_Typing ftenv fenv x f ft m)) ->

(** PPE cases *)
       
(* Modify *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv)
               (T1 T2 : Type) (VT1 : ValTyp T1) (VT2 : ValTyp T2)
               (XF: XFun T1 T2) (q : QValue)
               (k : QValueTyping tenv q (vtyp T1)),
          PPE ftenv tenv fenv (Modify T1 T2 VT1 VT2 XF q) (vtyp T2)
              (Modify_Typing ftenv tenv fenv T1 T2 VT1 VT2 XF q k)) ->

(* Return *)
       (forall (G : Tag)
               (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
               (q : QValue) (t : VTyp)
               (k : QValueTyping tenv q t),
        PPE ftenv tenv fenv (Return G q) t
            (Return_Typing G ftenv tenv fenv q t k)) ->

(* BindN *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
               (e1 e2 : Exp) (t1 t2 : VTyp)
               (k1 : ExpTyping ftenv tenv fenv e1 t1)
               (k2 : ExpTyping ftenv tenv fenv e2 t2),
        PPE ftenv tenv fenv e1 t1 k1 ->
        PPE ftenv tenv fenv e2 t2 k2 ->
        PPE ftenv tenv fenv (BindN e1 e2) t2
            (BindN_Typing ftenv tenv fenv e1 e2 t1 t2 k1 k2)) ->
       
(* BindS *)       
       (forall (ftenv : funTC) (tenv tenv' : valTC) 
               (fenv : funEnv) (x : Id) (e1 e2 : Exp) (t1 t2 : VTyp)
               (h : tenv' = updateE tenv x t1)
               (k1 : ExpTyping ftenv tenv fenv e1 t1) 
               (k2 : ExpTyping ftenv tenv' fenv e2 t2),
        PPE ftenv tenv fenv e1 t1 k1 ->
        PPE ftenv tenv' fenv e2 t2 k2 ->
        PPE ftenv tenv fenv (BindS x e1 e2) t2
            (BindS_Typing ftenv tenv tenv' fenv x e1 e2 t1 t2 h k1 k2)) ->

(* BindMS *)       
       (forall (ftenv ftenvP ftenv' : funTC) (tenv tenvP tenv' : valTC)
               (fenv fenvP fenv' : funEnv) (envP : valEnv) 
               (e : Exp) (t : VTyp)
               (k1 : EnvTyping envP tenvP)
               (m1 : MatchEnvsT FunTyping fenv ftenv)
               (m2 : MatchEnvsT FunTyping fenvP ftenvP)
               (h1: tenv' = overrideE tenvP tenv)
               (h2: ftenv' = overrideE ftenvP ftenv)
               (h3: fenv' = overrideE fenvP fenv)
               (k2: ExpTyping ftenv' tenv' fenv' e t),
        PPE ftenv' tenv' fenv' e t k2 ->
        PPE ftenv tenv fenv (BindMS fenvP envP e) t
          (BindMS_Typing ftenv ftenvP ftenv' tenv tenvP tenv' fenv fenvP
             fenv' envP e t k1 m1 m2 h1 h2 h3 k2)) ->

(* Apply *)
       (forall (ftenv : funTC) (tenv fps : valTC) (fenv : funEnv)
               (q : QFun) (ps : Prms) (pt : PTyp) (t : VTyp)
               (h : pt = env2ptyp fps)
               (m : MatchEnvsT FunTyping fenv ftenv)
               (k1 : QFunTyping ftenv fenv q (FT fps t))
               (k2 : PrmsTyping ftenv tenv fenv ps pt),
        PPQ ftenv fenv q (FT fps t) k1 ->
        PPP ftenv tenv fenv ps pt k2 ->
        PPE ftenv tenv fenv (Apply q ps) t
            (Apply_Typing ftenv tenv fps fenv q ps pt t h m k1 k2)) ->

(* Val *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
               (v : Value) (t : VTyp)
               (k : ValueTyping v t),
          PPE ftenv tenv fenv (Val v) t
              (Val_Typing ftenv tenv fenv v t k)) ->

(* IfThenElse *)
       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv)
          (e1 e2 e3 : Exp) (t : VTyp)
          (k1 : ExpTyping ftenv tenv fenv e1 Bool)
          (k2 : ExpTyping ftenv tenv fenv e2 t)
          (k3 : ExpTyping ftenv tenv fenv e3 t),
        PPE ftenv tenv fenv e1 Bool k1 ->
        PPE ftenv tenv fenv e2 t k2 ->
        PPE ftenv tenv fenv e3 t k3 ->
        PPE ftenv tenv fenv (IfThenElse e1 e2 e3) t
           (IfThenElse_Typing ftenv tenv fenv e1 e2 e3 t k1 k2 k3)) ->

(** PPQ cases *)
       
(* PS *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
               (es : list Exp) (ts : list VTyp)
               (m : Forall2T (ExpTyping ftenv tenv fenv) es ts),
        SSL ftenv tenv fenv es ts m ->   
        PPP ftenv tenv fenv (PS es) (PT ts)
            (PS_Typing ftenv tenv fenv es ts m)) ->


(** PPP conclusion *)

       forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
              (ps : Prms) (pt : PTyp)
              (k: PrmsTyping ftenv tenv fenv ps pt),
       PPP ftenv tenv fenv ps pt k. 

Proof.
  intros PPF PPQ PPE PPP SSL SSA SSB.
  intros.
  revert ps pt k.
  revert ftenv tenv fenv.
  
  fix HP_P 6 with

  (HP_F (f : Fun) (ft : FTyp) (k: FunTyping f ft) {struct k}:
                                           PPF f ft k)
  (HP_E (ftenv : funTC) (tenv : valTC) (fenv : funEnv) (e : Exp)
        (v : VTyp) (k: ExpTyping ftenv tenv fenv e v) {struct k}:
                                           PPE ftenv tenv fenv e v k) 
  (HP_Q (ftenv : funTC) (fenv: funEnv) (h : QFun) (ft : FTyp)                           (k: QFunTyping ftenv fenv h ft) {struct k}:
                                           PPQ ftenv fenv h ft k).

(* PPP *)      
- intros.
  destruct k.
  apply X16.
  revert f.
  revert es ts.
  fix HP_QL 3.
  intros.
  destruct f.
  + apply X.
  + apply X0.
    * apply HP_QL.
    * apply HP_E.
(* PPF *)
- intros.
  destruct k.
  + apply X4.
    apply HP_E.
  + apply X5.
    apply HP_E.
    apply HP_F.
(* PPE *)  
- intros.
  destruct k.
  + apply X8.
  + apply X9.
  + apply X10.
    * apply HP_E.
    * apply HP_E.
  + apply X11.
    * apply HP_E.
    * apply HP_E.
  + apply X12.
    * apply HP_E.
  + apply X13.
    * apply HP_Q.
    * apply HP_P.
  + apply X14.
  + apply X15.
    * apply HP_E.
    * apply HP_E.
    * apply HP_E.
(* PPQ *)    
- intros.
  destruct k.
  + apply X6.
    apply HP_F.
  + apply X7.
    destruct m.
    * apply X3.
      {- revert m e e0 e1.
         revert ls2 ls1 ls5 ls6.
         fix HP_QA 5.
         intros.
         destruct m.
         + apply X1.
         + apply X2.
           * apply HP_QA with (ls5:=ls1 ++ (x, f) :: ls3)
                              (ls6:=ls2 ++ (x, ft) :: ls4).
             {- inversion e; subst.
                destruct (IdT.IdEqDec x k).
                + inversion H0.
                + reflexivity.
             }
             {- reflexivity. }
             {- reflexivity. }
           * apply HP_F.
      }       
      {- revert m0 e e0 e1.
         revert ls4 ls3 ls5 ls6.
         fix HP_QA 5.
         intros.
         destruct m0.
         + apply X1. 
         + apply X2.
           * apply HP_QA with (ls5:=ls1 ++ (x, f) :: ls0)
                                (ls6:=ls2 ++ (x, ft) :: ls3).
             {- assumption. }
             {- reflexivity. }
             {- reflexivity. }
           * apply HP_F.
      }      
      {- apply HP_F. }
Defined.

Definition ExpTypingP_str_rect PPF PPQ PPE PPP :=
  ExpTypingP_gen_str_rect PPF PPQ PPE PPP
       (Par_SSL PPE) (Par_SSA PPF) (Par_SSB PPF).
   

(***********************************************************************)


Lemma ExpTypingQ_gen_str_rect : forall 

(* properties *)
                        
         (PPF : forall (f : Fun) (ft : FTyp),
                  FunTyping f ft -> Type)
         
         (PPQ : forall (ftenv : funTC) (fenv : funEnv)
                       (q : QFun) (ft : FTyp),
                  QFunTyping ftenv fenv q ft -> Type)
         
         (PPE : forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
                       (e : Exp) (v : VTyp),
                  ExpTyping ftenv tenv fenv e v -> Type)
         
         (PPP : forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
                       (ps : Prms) (pt : PTyp),
                  PrmsTyping ftenv tenv fenv ps pt -> Type)
         
         (SSL : forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv)
                       (es: list Exp) (ts: list VTyp), 
		  Forall2T (ExpTyping ftenv tenv fenv) es ts -> Type)

         (SSA : forall (ftenv : funTC) (fenv: funEnv), 
		  MatchEnvsT FunTyping fenv ftenv -> Type)
         
         (SSB : forall (ftenv : funTC) (fenv: funEnv)
                       (x:Id) (f: Fun) (ft:FTyp), 
		  MatchEnvs2BT FunTyping x f ft fenv ftenv -> Type), 
                        
(** SSL cases **)
       
       (forall (ftenv : funTC) (tenv : valTC) (fenv: funEnv),
        SSL ftenv tenv fenv nil nil 
           (Forall2_nilT (ExpTyping ftenv tenv fenv))) ->

         
       (forall (ftenv : funTC) (tenv : valTC) (fenv: funEnv) 
               (es : list Exp) (ts : list VTyp)
               (e: Exp) (t: VTyp)
               (m1: ExpTyping ftenv tenv fenv e t)               
               (m2 : Forall2T (ExpTyping ftenv tenv fenv) es ts),
        SSL ftenv tenv fenv es ts m2 -> 
	PPE ftenv tenv fenv e t m1 ->  
	SSL ftenv tenv fenv (e::es) (t::ts)
         (Forall2_consT (ExpTyping ftenv tenv fenv) e t es ts m1 m2)) ->

(** SSA cases **)

       (SSA nil nil (MatchEnvs_NilT FunTyping)) ->

       
       (forall (ftenv : funTC) (fenv : funEnv)
               (x:Id) (f: Fun) (t: FTyp)
               (m1: FunTyping f t)
               (m2 : MatchEnvsT FunTyping fenv ftenv),
        SSA ftenv fenv m2 -> 
	PPF f t m1 ->  
        SSA ((x,t)::ftenv) ((x,f)::fenv)
            (MatchEnvs_ConsT FunTyping fenv ftenv x f t m1 m2)) ->

(** SSB cases **)

       (forall (ftenv ftenv0 ftenv1: funTC)
               (fenv fenv0 fenv1: funEnv)
               (x:Id) (f: Fun) (t: FTyp)
               (k: FunTyping f t)
               (m0 : MatchEnvsT FunTyping fenv0 ftenv0)
               (m1 : MatchEnvsT FunTyping fenv1 ftenv1)
               (h1 : findE ftenv0 x = None)
               (h2 : fenv = fenv0 ++ ((x,f)::fenv1))
               (h3 : ftenv = ftenv0 ++ ((x,t)::ftenv1)),                  
        SSA ftenv0 fenv0 m0 -> 
        SSA ftenv1 fenv1 m1 ->                                       
        PPF f t k -> 
        SSB ftenv fenv x f t
           (MatchEnvs2B_splitT FunTyping x f t 
               fenv ftenv fenv0 ftenv0 fenv1 ftenv1 k m0 m1 h1 h2 h3)) ->
         
(** PPF cases *)
      
(* FunZ *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
          (e0 e1 : Exp) (x : Id) (t : VTyp)
          (m : MatchEnvsT FunTyping fenv ftenv)
          (k : ExpTyping ftenv tenv fenv e0 t),
        PPE ftenv tenv fenv e0 t k ->
        PPF (FC fenv tenv e0 e1 x 0) (FT tenv t)
            (FunZ_Typing ftenv tenv fenv e0 e1 x t m k)) ->

(* FunS *)       
       (forall (ftenv ftenv' : funTC) (tenv : valTC) 
               (fenv fenv' : funEnv)
               (e0 e1 : Exp) (x : Id) 
               (n : nat) (t : VTyp)
               (h1 : ftenv' = updateE ftenv x (FT tenv t))
               (h2 : fenv' = updateE fenv x (FC fenv tenv e0 e1 x n))
               (m : MatchEnvsT FunTyping fenv ftenv)
               (k1 : ExpTyping ftenv' tenv fenv' e1 t)
               (k2 : FunTyping (FC fenv tenv e0 e1 x n) (FT tenv t)),
        PPE ftenv' tenv fenv' e1 t k1 ->
        PPF (FC fenv tenv e0 e1 x n) (FT tenv t) k2 ->
        PPF (FC fenv tenv e0 e1 x (S n)) (FT tenv t)
                (FunS_Typing ftenv ftenv' tenv fenv fenv'
                                      e0 e1 x n t h1 h2 m k1 k2)) ->
       
(** PPQ cases *)
       
(* QF *)       
       (forall (ftenv : funTC) (fenv : funEnv)
               (f : Fun) (ft : FTyp)
               (k : FunTyping f ft),
        PPF f ft k ->
        PPQ ftenv fenv (QF f) ft (QF_Typing ftenv fenv f ft k)) ->

(* FVar  *)       
       (forall (ftenv : funTC) (fenv : funEnv) (x : Id) 
               (f : Fun) (ft : FTyp)
               (m : MatchEnvs2BT FunTyping x f ft fenv ftenv),
        SSB ftenv fenv x f ft m ->     
        PPQ ftenv fenv (FVar x) ft (FVar_Typing ftenv fenv x f ft m)) ->

(** PPE cases *)
       
(* Modify *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv)
               (T1 T2 : Type) (VT1 : ValTyp T1) (VT2 : ValTyp T2)
               (XF: XFun T1 T2) (q : QValue)
               (k : QValueTyping tenv q (vtyp T1)),
          PPE ftenv tenv fenv (Modify T1 T2 VT1 VT2 XF q) (vtyp T2)
              (Modify_Typing ftenv tenv fenv T1 T2 VT1 VT2 XF q k)) ->

(* Return *)
       (forall (G : Tag)
               (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
               (q : QValue) (t : VTyp)
               (k : QValueTyping tenv q t),
        PPE ftenv tenv fenv (Return G q) t
            (Return_Typing G ftenv tenv fenv q t k)) ->

(* BindN *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
               (e1 e2 : Exp) (t1 t2 : VTyp)
               (k1 : ExpTyping ftenv tenv fenv e1 t1)
               (k2 : ExpTyping ftenv tenv fenv e2 t2),
        PPE ftenv tenv fenv e1 t1 k1 ->
        PPE ftenv tenv fenv e2 t2 k2 ->
        PPE ftenv tenv fenv (BindN e1 e2) t2
            (BindN_Typing ftenv tenv fenv e1 e2 t1 t2 k1 k2)) ->
       
(* BindS *)       
       (forall (ftenv : funTC) (tenv tenv' : valTC) 
               (fenv : funEnv) (x : Id) (e1 e2 : Exp) (t1 t2 : VTyp)
               (h : tenv' = updateE tenv x t1)
               (k1 : ExpTyping ftenv tenv fenv e1 t1) 
               (k2 : ExpTyping ftenv tenv' fenv e2 t2),
        PPE ftenv tenv fenv e1 t1 k1 ->
        PPE ftenv tenv' fenv e2 t2 k2 ->
        PPE ftenv tenv fenv (BindS x e1 e2) t2
            (BindS_Typing ftenv tenv tenv' fenv x e1 e2 t1 t2 h k1 k2)) ->

(* BindMS *)       
       (forall (ftenv ftenvP ftenv' : funTC) (tenv tenvP tenv' : valTC)
               (fenv fenvP fenv' : funEnv) (envP : valEnv) 
               (e : Exp) (t : VTyp)
               (k1 : EnvTyping envP tenvP)
               (m1 : MatchEnvsT FunTyping fenv ftenv)
               (m2 : MatchEnvsT FunTyping fenvP ftenvP)
               (h1: tenv' = overrideE tenvP tenv)
               (h2: ftenv' = overrideE ftenvP ftenv)
               (h3: fenv' = overrideE fenvP fenv)
               (k2: ExpTyping ftenv' tenv' fenv' e t),
        PPE ftenv' tenv' fenv' e t k2 ->
        PPE ftenv tenv fenv (BindMS fenvP envP e) t
          (BindMS_Typing ftenv ftenvP ftenv' tenv tenvP tenv' fenv fenvP
             fenv' envP e t k1 m1 m2 h1 h2 h3 k2)) ->

(* Apply *)
       (forall (ftenv : funTC) (tenv fps : valTC) (fenv : funEnv)
               (q : QFun) (ps : Prms) (pt : PTyp) (t : VTyp)
               (h : pt = env2ptyp fps)
               (m : MatchEnvsT FunTyping fenv ftenv)
               (k1 : QFunTyping ftenv fenv q (FT fps t))
               (k2 : PrmsTyping ftenv tenv fenv ps pt),
        PPQ ftenv fenv q (FT fps t) k1 ->
        PPP ftenv tenv fenv ps pt k2 ->
        PPE ftenv tenv fenv (Apply q ps) t
            (Apply_Typing ftenv tenv fps fenv q ps pt t h m k1 k2)) ->

(* Val *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
               (v : Value) (t : VTyp)
               (k : ValueTyping v t),
          PPE ftenv tenv fenv (Val v) t
              (Val_Typing ftenv tenv fenv v t k)) ->

(* IfThenElse *)
       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv)
          (e1 e2 e3 : Exp) (t : VTyp)
          (k1 : ExpTyping ftenv tenv fenv e1 Bool)
          (k2 : ExpTyping ftenv tenv fenv e2 t)
          (k3 : ExpTyping ftenv tenv fenv e3 t),
        PPE ftenv tenv fenv e1 Bool k1 ->
        PPE ftenv tenv fenv e2 t k2 ->
        PPE ftenv tenv fenv e3 t k3 ->
        PPE ftenv tenv fenv (IfThenElse e1 e2 e3) t
           (IfThenElse_Typing ftenv tenv fenv e1 e2 e3 t k1 k2 k3)) ->

(** PPQ cases *)
       
(* PS *)       
       (forall (ftenv : funTC) (tenv : valTC) (fenv : funEnv) 
               (es : list Exp) (ts : list VTyp)
               (m : Forall2T (ExpTyping ftenv tenv fenv) es ts),
        SSL ftenv tenv fenv es ts m ->   
        PPP ftenv tenv fenv (PS es) (PT ts)
            (PS_Typing ftenv tenv fenv es ts m)) ->


(** PPQ conclusion *)

       forall (ftenv : funTC) (fenv : funEnv)
              (q : QFun) (ft : FTyp)
              (k: QFunTyping ftenv fenv q ft), 
       PPQ ftenv fenv q ft k.
       
Proof.
  intros PPF PPQ PPE PPP SSL SSA SSB.
  intros.
  revert q ft k.
  revert ftenv fenv.
  
  fix HP_Q 5 with

  (HP_F (f : Fun) (ft : FTyp) (k: FunTyping f ft) {struct k}:
                                           PPF f ft k)
  (HP_E (ftenv : funTC) (tenv : valTC) (fenv : funEnv) (e : Exp)
        (v : VTyp) (k: ExpTyping ftenv tenv fenv e v) {struct k}:
                                           PPE ftenv tenv fenv e v k) 
  (HP_P (ftenv : funTC) (tenv : valTC) (fenv: funEnv) (ps : Prms) (ts : PTyp) 
       (k: PrmsTyping ftenv tenv fenv ps ts) {struct k}: 
                                           PPP ftenv tenv fenv ps ts k).

(* PPQ *)    
- intros.
  destruct k.
  + apply X6.
    apply HP_F.
  + apply X7.
    destruct m.
    * apply X3.
      {- revert m e e0 e1.
         revert ls2 ls1 ls5 ls6.
         fix HP_QA 5.
         intros.
         destruct m.
         + apply X1.
         + apply X2.
           * apply HP_QA with (ls5:=ls1 ++ (x, f) :: ls3)
                              (ls6:=ls2 ++ (x, ft) :: ls4).
             {- inversion e; subst.
                destruct (IdT.IdEqDec x k).
                + inversion H0.
                + reflexivity.
             }
             {- reflexivity. }
             {- reflexivity. }
           * apply HP_F.
      }       
      {- revert m0 e e0 e1.
         revert ls4 ls3 ls5 ls6.
         fix HP_QA 5.
         intros.
         destruct m0.
         + apply X1. 
         + apply X2.
           * apply HP_QA with (ls5:=ls1 ++ (x, f) :: ls0)
                                (ls6:=ls2 ++ (x, ft) :: ls3).
             {- assumption. }
             {- reflexivity. }
             {- reflexivity. }
           * apply HP_F.
      }      
      {- apply HP_F. }
(* PPF *)
- intros.
  destruct k.
  + apply X4.
    apply HP_E.
  + apply X5.
    apply HP_E.
    apply HP_F.
(* PPE *)  
- intros.
  destruct k.
  + apply X8.
  + apply X9.
  + apply X10.
    * apply HP_E.
    * apply HP_E.
  + apply X11.
    * apply HP_E.
    * apply HP_E.
  + apply X12.
    * apply HP_E.
  + apply X13.
    * apply HP_Q.
    * apply HP_P.
  + apply X14.
  + apply X15.
    * apply HP_E.
    * apply HP_E.
    * apply HP_E.
(* PPP *)      
- intros.
  destruct k.
  apply X16.
  revert f.
  revert es ts.
  fix HP_QL 3.
  intros.
  destruct f.
  + apply X.
  + apply X0.
    * apply HP_QL.
    * apply HP_E.
Defined.


Definition ExpTypingQ_str_rect PPF PPQ PPE PPP :=
  ExpTypingQ_gen_str_rect PPF PPQ PPE PPP
       (Par_SSL PPE) (Par_SSA PPF) (Par_SSB PPF).
   

End StaticInduct.


      
      
  
      
      
  


      
      
  
      
      
  