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
Require Import QafnySyntax.
Require Import LocusDef.
Require Import LocusKind.
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

Lemma perm_env_is_equiv: forall T1 T2, perm_envs T1 T2 -> env_equiv T1 T2.
Proof.
  intros. induction H. constructor.
  apply env_trans with (T2 := T2). inv H.
  apply env_mut. easy.
Qed.

Lemma perm_envs_app: forall T1 T2 T, perm_envs T1 T2 -> perm_envs (T1++T) (T2++T).
Proof.
  intros. induction H. constructor.
  inv H. apply perm_env_many with (T2 := (((l1 ++ y :: x :: l2, v) :: S) ++ T)); try easy.
Qed.

Lemma type_state_elem_same_unique: forall a t t', 
  type_state_elem_same t a -> type_state_elem_same t' a -> t = t'.
Proof.
  intros. induction H. inv H0. easy. inv H0. easy. inv H0. easy.
Qed.

Definition add_a (a:range) (T:type_map) :=
   match T with nil => nil | (x,y)::l => (a::x,y)::l end.

Lemma perm_envs_same_length: forall T T1, perm_envs T T1 ->  length T = length T1.
Proof.
  intros. induction H; try easy. inv H. simpl in *. easy.
Qed.

Definition is_cval_t (l: type_map) := match l with nil => True | ((x,CH)::l) => True | _ => False end.

Lemma is_cval_t_subst: forall l x a, is_cval_t (subst_type_map l x a) -> forall v,is_cval_t (subst_type_map l x v).
Proof.
  intros. unfold is_cval_t in *.
  destruct (subst_type_map l x a) eqn:eq1. destruct l. simpl in *. easy.
  simpl in *. destruct p. inv eq1.
  destruct (subst_type_map l x v) eqn:eq2. easy.
  destruct p. destruct p0. simpl in *.
  destruct l. simpl in *. easy.
  simpl in *. destruct p. simpl in *. inv eq1. inv eq2. easy.
Qed.

Lemma length_subst: forall l x a, forall v, length (subst_type_map l x a) = length (subst_type_map l x v).
Proof.
  intros. induction l; try easy.
  simpl in *. destruct a0. simpl in *. rewrite IHl. easy.
Qed.

Lemma perm_envs_cong: forall T T' a, perm_envs T T' -> perm_envs (add_a a T) (add_a a T').
Proof.
  intros. induction H. constructor.
  unfold add_a in *. destruct T2.
  inv H. apply perm_envs_same_length in H0 as X1. simpl in *. destruct T3; try easy.
  apply perm_envs_same_length in H0 as X2. simpl in *. destruct T1; try easy.
  destruct p. destruct p0. destruct p1.
  apply perm_env_many with (T2 := ((a :: l, s) :: T2)); try easy.
  inv H. rewrite app_comm_cons. rewrite app_comm_cons with (a := a).
  constructor.
Qed.

Definition add_end a (T:type_map) :=
   match T with nil => nil | (x,y)::l => (x++a,y)::l end.

Lemma perm_envs_prog: forall T T' a, perm_envs T T' -> perm_envs (add_end a T) (add_end a T').
Proof.
  intros. induction H. constructor.
  unfold add_end in *. destruct T2.
  inv H. apply perm_envs_same_length in H0 as X1. simpl in *. destruct T3; try easy.
  apply perm_envs_same_length in H0 as X2. simpl in *. destruct T1; try easy.
  destruct p. destruct p0. destruct p1.
  apply perm_env_many with (T2 := ((l++a, s) :: T2)); try easy.
  inv H. repeat rewrite <- app_assoc. repeat rewrite <- app_comm_cons.
  constructor.
Qed.

Lemma perm_envs_end: forall a l, perm_envs ([(a::l,CH)]) ([(l++[a],CH)]).
Proof.
  intros. induction l. simpl in *. constructor.
  simpl in *.
  apply perm_env_many with (T2 := [(a0 :: a :: l, CH)]).
  replace ((a :: a0 :: l)) with ([]++a :: a0 :: l) by easy.
  replace (a0 :: a :: l) with ([] ++ (a0 :: a :: l)) by easy.
  apply perm_env_rule. apply perm_envs_cong with (a := a0) in IHl.
  unfold add_a in *. easy.
Qed.

Lemma perm_envs_single_prog: forall T T', perm_envs T T' ->
   is_cval_t T -> length T <= 1 -> is_cval_t T' /\ length T' = length T.
Proof.
  intros. induction H. easy.
  assert (is_cval_t T2 /\ length T2 = length T1).
  inv H. simpl in *. destruct v; try easy.
  destruct H3. apply IHperm_envs in H3; try lia. destruct H3.
  split; try easy. rewrite H5. easy.
Qed.

Lemma env_equiv_single_prog: forall T T', env_equiv T T' ->
   is_cval_t T -> length T <= 1 -> is_cval_t T' /\ length T' = length T.
Proof.
  intros. induction H. easy.
  unfold is_cval_t in *. simpl in *. destruct v; try easy. inv H. split. easy.
  lia.
  unfold is_cval_t in *. destruct v; try easy.
  simpl in *. destruct x; try easy.
  destruct s; try easy. split; try easy.
  assert (length T1 = 0) by lia.
  destruct T1; try easy. simpl in *.
  assert (is_cval_t T2 /\ length T2 = 0). apply IHenv_equiv; try easy. lia.
  destruct H3; try easy. rewrite H4. easy.
Qed.

Lemma env_equiv_add_a: forall T T' a, env_equiv T T' -> env_equiv (add_a a T) (add_a a T').
Proof.
  intros. induction H. constructor.
  unfold add_a in *. 
  apply env_subtype. easy.
  unfold add_a in *.
  rewrite app_comm_cons.
  rewrite app_comm_cons.
  apply env_mut.
  unfold add_a in *. destruct x.
  destruct T1; try easy. inv H. constructor.
  destruct T2; try easy. destruct p. destruct p0.
  apply env_cong. easy.
Qed.

Lemma env_equiv_add_end: forall T T' a, env_equiv T T' -> env_equiv (add_end a T) (add_end a T').
Proof.
  intros. induction H; simpl in *; try constructor.
  easy.
  repeat rewrite <- app_assoc.
  repeat rewrite <- app_comm_cons.
  apply env_mut.
  destruct x. apply env_cong. easy.
Qed.

Lemma env_equiv_end: forall a l, env_equiv ([(a::l,CH)]) ([(l++[a],CH)]).
Proof.
  intros. induction l. simpl in *. constructor.
  simpl in *.
  assert (env_equiv ([(a0 :: a :: l, CH)]) ([(a0 :: l ++ [a], CH)])).
  apply env_equiv_add_a with (a := a0) in IHl. easy.
  apply env_trans with (T2 := [(a0 :: a :: l, CH)]); try easy.
  replace ((a :: a0 :: l)) with ([]++a :: a0 :: l) by easy.
  replace (a0 :: a :: l) with ([] ++ (a0 :: a :: l)) by easy.
  apply env_mut.
Qed.

Inductive locus_system {rmax:nat}
           : mode -> aenv -> type_map -> pexp -> type_map -> Prop :=

    | eq_ses : forall q env s T T' T1,
         locus_system q env T s T' -> env_equiv T' T1 -> locus_system q env T s T1

    | sub_ses: forall q env s T T' T1,
        locus_system q env T s T' -> locus_system q env (T++T1) s (T'++T1)

    | skip_ses : forall q env, locus_system q env nil (PSKIP) nil
    | assign_ses : forall q env x a e T T', type_aexp env a (CT,nil) -> ~ AEnv.In x env ->
              locus_system q (AEnv.add x (CT) env) T e T' -> locus_system q env T (Let x a e) T'
    | meas_m1 : forall env x y e n l T T', AEnv.MapsTo y (QT n) env -> ~ AEnv.In x env ->
               locus_system CM (AEnv.add x (CT) env) ((l,CH)::T) e T'
              -> locus_system CM env (((y,BNum 0,BNum n)::l,CH)::T) (Let x (Meas y) e) T'
    | appu_ses_nor : forall q env l e n, type_exp env e (QT n,l) -> oracle_prop env l e ->
                           locus_system q env ([(l, TNor)]) (AppU l e) ([(l, TNor)])

    | appu_ses_ch : forall q env l l' e n, type_exp env e (QT n,l) -> oracle_prop env l e ->
                           locus_system q env ([(l++l', CH)]) (AppU l e) ([(l++l', CH)])


    | appu_ses_h_nor:  forall q env p a m, type_vari env p (QT m, [a]) -> simp_varia env p a ->
                    locus_system q env ([([a], TNor)]) (AppSU (RH p)) ([([a], THad)])
    | appu_ses_h_had:  forall q env p a m, type_vari env p (QT m, [a]) -> simp_varia env p a ->
                    locus_system q env ([([a], THad)]) (AppSU (RH p)) ([([a], TNor)])

    | appu_ses_h_ch:  forall q env p a l m, type_vari env p (QT m, [a]) -> simp_varia env p a ->
                    locus_system q env ([([a]++l, CH)]) (AppSU (RH p)) ([([a]++l, CH)])

    | qif_ses: forall q env T b e, type_bexp env b (CT,nil) ->
                      locus_system q env T e T -> locus_system q env T (If b e) T

    | qif_ses_ch: forall q env b n l l1 e, type_bexp env b (QT n,l) ->
                locus_system QM env ([(l1,CH)]) e ([(l1,CH)])
             -> locus_system q env ([(l++l1,CH)]) (If b e) ([(l++l1,CH)])

 (*   | dif_ses_ch: forall q env T p n l l' t, type_vari env p (QT n,l) -> find_type T l (Some (l',t)) ->
                 locus_system q env T (Diffuse p) ([(l',CH)]) *)
    | pseq_ses_type: forall q env T e1 e2 T1 T2, locus_system q env T e1 T1 ->
                       locus_system q env T1 e2 T2 ->
                       locus_system q env T (PSeq e1 e2) T2
    | qfor_ses_no: forall q env T i l h b e, h <= l -> locus_system q env T (For i (Num l) (Num h) b e) T
    | qfor_ses_ch: forall q env T i l h b e, l < h -> ~ AEnv.In i env ->
        (forall v, l <= v < h -> locus_system q env (subst_type_map T i v) 
                           (If (subst_bexp b i v) (subst_pexp e i v)) (subst_type_map T i (v+1)))
              -> locus_system q env (subst_type_map T i l) 
                           (For i (Num l) (Num h) b e) (subst_type_map T i h).




