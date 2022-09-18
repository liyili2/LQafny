Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import OQASM.
Require Import OQIMP.
Require Import Session.
(**********************)
(** Unitary Programs **)
(**********************)

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Declare Scope pexp_scope.
Delimit Scope pexp_scope with pexp.
Local Open Scope pexp_scope.
Local Open Scope nat_scope.

Definition session :Set := (var * nat * nat).
Definition atpred_elem :Type := (list session * se_type).
Definition atpred := list atpred_elem.

Inductive state :Type :=
             | SA (x:varia) (l:list (varia * state))
             | qket (i:var) (n:aexp) (p:aexp) (b:bexp)
             | upP (e:state) (i:aexp) (a:aexp)
             | SITE (i:var) (x:bool) (e1:state) (e2:bool -> bool)
             | Join (e1:state) (e2:state)
             | CreateEn (m:nat) (n:nat) (l:list session)
             | Sigma (i:var) (l:aexp) (n:aexp) (p:aexp) (b:aexp) (* represent 1/sqrt{2^n} Sigma^n_{i=b} (p,b) *)
             | Tensor (s1:list state) (* tensor of list of states, avoiding associativy definition *)
             (* | Plus (s1:state) (s2:state) |x> + |y> state. x and y are not equal *)

             | NTensor (i:var) (l:aexp) (n:aexp) (b:aexp) (b:bexp) (* represent Tensor^n_{i=b} s *).

Inductive cpred_elem := PFalse | CState (b:bexp) 
             | QState (x:state) (s:state)
             | QIn (p:aexp) (x:aexp) (s:state) (* (p,x) \in Sigma s. *)
             | PNot (p:cpred_elem) | CForall (xs:list var) (p1:list cpred_elem) (p2:cpred_elem)
             | Valid (range:bexp) (b:bexp).

Definition cpred := list cpred_elem.
Definition fresh (l:nat) := l +1.



Section Triple. 

  Variable qenv : var -> nat.
  Variable env : aenv.
  Variable amode: atype.

  Axiom subst_state : cpred -> list session -> state -> cpred.
  Axiom subst_nat : cpred -> var -> aexp -> cpred.
  Axiom subst_nat_t : tpred -> var -> aexp -> tpred.
  Axiom match_state: varia -> list session -> (var * nat * nat * cpred).

  Axiom session_check: cpred -> atpred -> pexp -> atpred -> Prop.

  Axiom sat_num : cpred -> aexp -> nat -> Prop.

  Definition flip_x (x:bool) := negb x.

  Definition apply_x (x:var) (n1 n2 :nat) (new:var) :=
     SITE new ((n1 <=? new) && (new <? n2)) (SA (Var x) nil) (flip_x).

  Definition create_en (n:nat) (m:nat) (l:list session) := CreateEn n m l.

  Inductive triple {env:aenv} {qenv: var -> nat} 
            : (var * atpred * cpred) -> pexp -> (var * atpred * cpred)  -> Prop :=
      | tpred_comm : forall v t1 t2 S e Q, triple (v,(t1++t2),S) e Q -> triple (v,(t2++t1),S) e Q
      | cpred_comm_1 : forall T v S1 S2 Q e, triple (v,T,S1++S2) e Q -> triple (v,T,S2++S1) e Q
      | cpred_comm_2 : forall T v S1 S2 Q e, triple Q e (v,T,S1++S2) -> triple Q e (v,T,S2++S1)
      | appX_1 : forall new x n1 n2 m p t x_var T S Q,
                  session_check S ([([(x,n1,n2)],THT m (TNor p))]) (AppU X_gate x_var) ([t]) ->
                  match_state x_var ([(x,n1,n2)]) = (x,n1,n2,Q) ->
                  triple (new, ([(x,n1,n2)],THT m (TNor p))::T,subst_state S ([(x,n1,n2)]) (apply_x x n1 n2 new))
                      (AppU X_gate x_var)
                       (fresh new, t::T,Q++S)
      | if_en : forall new b e l n m r t T T' S,
                  session_check S T (If b e) ((l,THT n (EN r (TMore m t)))::T') ->
                  triple (new, T, subst_state S l (create_en n m l))
                      (If b e) (new, (l,THT n (EN r (TMore m t)))::T', S)
      | qwhile : forall new n nv x i b e T S,
                  sat_num S n nv ->
                  (forall (iv:nat), iv < nv ->
                       session_check S (subst_nat_t T i (Num iv)) (If b e) (subst_nat_t T i (Num (iv+1)))) ->
                triple (new, T, (CState (BLt (BA (Var i)) n))::S) (If b e) 
                   (new,subst_nat_t T i (APlus (BA (Var i)) (Num 1)),subst_nat S i (APlus (BA (Var i)) (Num 1))) ->
                  triple (new, T, S) (QWhile n x i b e) (new, subst_nat_t T i n, subst_nat S i n).


End Triple.



















