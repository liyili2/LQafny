Require Import Reals.
Require Import Psatz.
Require Import Complex.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat Permutation. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import DisQSyntax.
Require Import DisQDef.
Require Import DisQKind.
Require Import DisQSem.
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

(* Type system -- The Static Type system, 
   and the dynamic gradual typing part will be merged with the triple rule. *)

(* Type system for oqasm. *)


Definition bits := list bool.

Definition get_cus (n:nat) (f:posi -> val) (x:var) := 
          fun i => if i <? n then (match f (x,i) with nval b r => b | _ => false end) else allfalse i.

Definition rotate (r :rz_val) (q:nat) := addto r q.

Definition times_rotate (v : val) (q:nat) := 
     match v with nval b r => if b then nval b (rotate r q) else nval b r
                  | qval rc r =>  qval rc (rotate r q)
     end.

Fixpoint sr_rotate' (st: posi -> val) (x:var) (n:nat) (size:nat) :=
   match n with 0 => st
              | S m => (sr_rotate' st x m size)[(x,m) |-> times_rotate (st (x,m)) (size - m)]
   end.
Definition sr_rotate st x n := sr_rotate' st x (S n) (S n).

Definition r_rotate (r :rz_val) (q:nat) := addto_n r q.

Definition tenv : Type := (locus * rz_val). 
    (* varaible -> global phase rz_val : nat -> bool (nat), nat -> bool (nat) |0010101> *)
Fixpoint find_pos' (p:posi) (l:list (var*nat*nat)) (pos:nat) :=
   match l with [] => 0
              | (x,n,m)::xs => if (x =? fst p) && (n <=? snd p) && (snd p <? m)
                               then (pos + (snd p) - n)
                               else find_pos' p xs (pos + m - n)
   end.
Definition find_pos p l := find_pos' p l 0.

Inductive add_to_types' : type_map -> type_map -> type_map -> Prop :=
   add_to_empty: forall T, add_to_types' T [] T
 | add_to_many_1: forall T T' s t T1, In s (dom T) -> add_to_types' T T' T1 -> add_to_types' T ((s,t)::T') T1
 | add_to_many_2: forall T T' s t T1, ~ In s (dom T) -> add_to_types' T T' T1 -> add_to_types' T ((s,t)::T') ((s,t)::T1).

Inductive add_to_types : type_map -> type_map -> type_map -> Prop :=
   add_to_type_rule: forall T T1 T2 T3, env_equiv T1 T2 -> add_to_types' T T2 T3 -> add_to_types T T1 T3.

Fixpoint subst_type_map (l:type_map) (x:var) (n:nat) :=
  match l with nil => nil
          | (y,v)::yl => (subst_locus y x n,v)::(subst_type_map yl x n)
  end.

Inductive mode := CM | QM.

Inductive perm_env: type_map -> type_map -> Prop :=
  perm_env_rule: forall l1 l2 x y v S, perm_env ((l1++x::y::l2,v)::S) ((l1++y::x::l2,v)::S).

Inductive perm_envs: type_map -> type_map -> Prop :=
   perm_env_empty: forall T, perm_envs T T
 | perm_env_many: forall T1 T2 T3, perm_env T1 T2 -> perm_envs T2 T3 -> perm_envs T1 T3.

Axiom perm_envs_sym: forall T1 T2, perm_envs T1 T2 -> perm_envs T2 T1.

Fixpoint has_mea_aux (p: process) :=
  match p with PNil => false
             | (PIf _ p q) => orb (has_mea_aux p) (has_mea_aux q)
             | (AP (CMeas _ _) p) => true
             | (AP _ p) => has_mea_aux p
             | (DP _ p) => has_mea_aux p
  end.
    
Definition has_mea (lp:list process) := filter has_mea_aux lp.
Definition has_no_mea (lp:list process) := filter (fun i => negb (has_mea_aux i)) lp.
Fixpoint locus_with_mea_aux (p: process) :=
  match p with PNil => nil
           |(PIf _ p q) => locus_with_mea_aux p ++ locus_with_mea_aux q
           |(AP (CMeas _ k) p) => k::(locus_with_mea_aux p)
           |(AP _ p) => locus_with_mea_aux p 
           | (DP _ p) => locus_with_mea_aux p
  end.
Fixpoint locus_with_mea (lp:list process) :=
  match lp with nil => nil
           | p::ps => (locus_with_mea_aux p) ++ (locus_with_mea ps) end.

Inductive AllSame {A : Type} : list A -> Prop :=
| AllSame_nil : AllSame nil
| AllSame_singleton : forall x, AllSame (x::nil)
| AllSame_cons : forall x y l, x = y -> AllSame (y::l) -> AllSame (x::y::l).

Inductive GroupByB {A B : Type} : list (A * B) -> list (list A * B) -> Prop :=
| GroupByB_nil : GroupByB nil nil
| GroupByB_cons : forall a b l l' la, GroupByB l l' -> GroupByB ((a, b)::l) (((a::la),b)::l').

Inductive gmap_map : var -> type_gmap -> type_map -> Prop :=
  | glocus_zero : forall l, gmap_map l nil nil
| glocus_many : forall s e l a T T' g g', gmap_map l T T' -> GroupByB g g' ->In e g' -> e = (a,l) -> gmap_map l ((g,s)::T) ((a,s)::T').
(* Convert gmap to map based on input location l*)

(******** DisQ Type System **********)
(** We define this type system in three levels: process-level, membrane-level and config-level. **)

(** Process-level type **)
Inductive p_locus_system {rmax:nat}
           : aenv -> type_map -> process -> type_map -> Prop :=

    | eq_ses : forall env s T T' T1,
         p_locus_system env T s T' -> env_equiv T' T1 -> p_locus_system env T s T1
    | sub_ses: forall env s T T' T1,
        p_locus_system env T s T' -> p_locus_system env (T++T1) s (T'++T1)
    | skip_ses : forall env, p_locus_system env nil (PNil) nil
    | meas_ses : forall env x y e n l T T' lc Q k, AEnv.MapsTo y (QT lc n) env -> ~ AEnv.In x env ->
               p_locus_system (AEnv.add x (CT) env) ((l,CH)::T) e T' -> k = [(y, BNum 0, BNum n)]
               -> p_locus_system env ((k++l,CH)::T) (AP (CMeas x k) Q)  T'
    | op_ses : forall env t k l e T T' Q, oracle_prop env k e -> 
                     p_locus_system env ((k++l,t)::T) Q T' ->
                         p_locus_system env ((k++l,t)::T) (AP (CAppU k e) Q) T'
    | qif_ses : forall env T T' b P Q, p_locus_system env T P T' -> p_locus_system env T Q T' ->
                                        p_locus_system env T (PIf b P Q) T'
    | send_ses : forall env a v T T' Q,  AEnv.MapsTo a (CT) env -> type_aexp env v (CT,nil) -> 
                               p_locus_system env T Q T' ->
                               p_locus_system env T (DP (Send a v) Q) T'
    | recv_ses : forall env a x T T' Q, AEnv.MapsTo a (CT) env -> 
                                          p_locus_system (AEnv.add x (CT) env) T Q T' ->
                                          p_locus_system env T (DP (Recv a x) Q) T'
.

Inductive p_locus_systems {rmax:nat}
           : aenv -> type_map -> list process -> type_map -> Prop :=
   | type_single : forall env T, p_locus_systems env T nil T
   | type_many : forall env P Q T T1 T2, @p_locus_system rmax env T P T1
          -> p_locus_systems env T1 Q T2 -> p_locus_systems env T1 (P::Q) T2
.

Inductive p_locus_system_mea {rmax:nat}
           : aenv -> type_map -> list process -> type_map -> Prop :=
   | meatype_single : forall env, p_locus_system_mea env nil nil nil
   | meatype_many : forall env P Q T T1 T2 T3, @p_locus_system rmax env T P T1
          -> p_locus_system_mea env T2 Q T3 -> p_locus_system_mea env (T1++T2) (P::Q) (T2++T3).

Definition all_same_loc (g:glocus) (l:var) :=
   forall v la, In (v, la) g -> la = l.

Definition no_loc (g:glocus) (l:var) :=
   forall v la, In (v, la) g -> la <> l.

(** Membrane-level type **)
Inductive m_locus_system {rmax:nat}
           : var -> aenv -> type_map -> memb -> type_map -> Prop :=
   (* | meq_ses : forall env s T T' T1,
         m_locus_system env T s T' -> genv_equiv T' T1 -> m_locus_system env T s T1 
    | msub_ses: forall env s T T' T1 cfg,
         m_locus_system env cfg T s T' -> m_locus_system env cfg (T++T1) s (T'++T1)
   *)
    | newv_ses :  forall env x n m T T' l,
         m_locus_system l (AEnv.add x (QT l n) env) (([((x, BNum 0, BNum n))],CH)::T) m T' -> 
         m_locus_system l env T (NewVMemb x n m) T'
    | newc_ses :  forall env x n m T T' l,
         m_locus_system l (AEnv.add x (QT l n) env) (([((x, BNum 0, BNum n))],CH)::T) m T' 
             -> m_locus_system l env T (NewCMemb x n m) T'
    | mem_sys : forall l m nm Ta Tb T T' env lp, m = has_mea lp 
                  -> nm = has_no_mea lp -> @p_locus_system_mea rmax env T m  Ta
                -> @p_locus_systems rmax env T' m  Tb
                   -> m_locus_system l env (T++T') (Memb lp) (Ta++Tb).

Inductive has_no_l : var -> type_gmap -> Prop :=
   has_no_l_empty: forall x, has_no_l x nil
 | has_no_l_many: forall x a b M, no_loc a x -> has_no_l x M -> has_no_l x ((a,b)::M).

Inductive all_l : var -> type_gmap -> Prop :=
   all_l_empty: forall x, all_l x nil
 | all_l_many: forall x a b M, all_same_loc a x -> all_l x M -> all_l x ((a,b)::M).

(** Config-level type **)
Inductive c_locus_system {rmax:nat}
           : aenv -> type_gmap -> config -> type_gmap -> Prop :=
| nil_ses : forall env T, c_locus_system env T nil T 
| top_ses : forall env m ms Tl Tl' Ta Tb l T T', has_no_l l T -> all_l l Tl
   -> gmap_map l Tl Ta -> gmap_map l Tl' Tb ->
        @m_locus_system l rmax env Ta m Tb ->
        c_locus_system env T ms T' ->
        c_locus_system env (Tl++T) ((m,l)::ms) (Tl'++T').
                         

