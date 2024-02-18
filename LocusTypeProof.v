Require Import Reals.
Require Import Psatz.
Require Import Complex.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat Permutation. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import OQASM.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import QafnySyntax.
Require Import LocusDef.
Require Import LocusKind.
Require Import LocusSem.
Require Import LocusType.
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

Inductive env_state_eq : type_map -> qstate ->  Prop :=
    env_state_eq_empty : env_state_eq nil nil
  | env_state_eq_many : forall s t a l1 l2, env_state_eq l1 l2 -> type_state_elem_same t a -> env_state_eq ((s,t)::l1) ((s,a)::l2).

Definition qstate_wt (S : qstate) : Prop := forall s m bl, In (s,Cval m bl) S -> m > 0.


Lemma env_state_eq_app: forall S a1 a2, env_state_eq (a1++a2) S
      -> exists b1 b2, env_state_eq (a1++a2) (b1++b2) /\ S = b1 ++ b2 /\ length b1 = length a1.
Proof.
  intros. remember (a1++a2) as S1.
  generalize dependent a1.
  generalize dependent a2.
  induction H. intros. symmetry in HeqS1. apply app_eq_nil in HeqS1. inv HeqS1.
  exists nil,nil. split. simpl. constructor. simpl. easy.
  intros. destruct a1. simpl in *. destruct a2. inv HeqS1.
  inv HeqS1.
  specialize (IHenv_state_eq a2 nil).
  simpl in *. assert (a2 = a2) by easy. apply IHenv_state_eq in H1.
  destruct H1 as [b1 [b2 [X1 [X2 X3]]]].
  exists b1. exists ((s,a)::b2).
  rewrite length_zero_iff_nil in X3 ; subst. simpl in *.
  split. constructor. easy. easy. easy.
  inv HeqS1.
  specialize (IHenv_state_eq a2 a1).
  assert (a1 ++ a2 = a1 ++ a2) by easy. apply IHenv_state_eq in H1.
  destruct H1 as [b1 [b2 [X1 [X2 X3]]]].
  exists ((s, a)::b1). exists b2.
  split. simpl. constructor. easy. easy.
  split. simpl. rewrite X2. easy. simpl. rewrite X3. easy.
Qed.

Lemma env_state_eq_same_length: forall a1 a2 b1 b2, length a1 = length b1
        -> env_state_eq (a1++a2) (b1++b2) -> env_state_eq a1 b1 /\ env_state_eq a2 b2.
Proof.
  induction a1;intros;simpl in *.
  symmetry in H. apply length_zero_iff_nil in H as X1; subst. simpl in *.
  split. constructor. easy. destruct b1. simpl in *. easy.
  simpl in *. inv H.
  inv H0.
  destruct (IHa1 a2 b1 b2 H2 H4) as [X1 X2].
  split. constructor; easy. easy.
Qed.

Lemma env_state_eq_app_join: forall a1 a2 b1 b2, env_state_eq a1 b1 -> env_state_eq a2 b2 -> env_state_eq (a1++a2) (b1 ++ b2).
Proof.
  induction a1; intros; simpl in *.
  inv H. simpl. easy.
  inv H. simpl in *. constructor. apply IHa1; easy. easy.
Qed.

Lemma env_state_eq_app_comm: forall a1 a2 b1 b2, length a1 = length b1 -> env_state_eq (a1 ++ a2) (b1++b2) -> env_state_eq (a2 ++ a1) (b2++b1).
Proof.
  intros. remember (a1 ++ a2) as l1. remember (b1 ++ b2) as l2.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent b1.
  generalize dependent b2.
  induction H0. intros.
  symmetry in Heql1. symmetry in Heql2.
  apply app_eq_nil in Heql1. apply app_eq_nil in Heql2. inv Heql1. inv Heql2.
  simpl. constructor.
  intros.
  destruct a1. simpl in *. symmetry in H1. rewrite length_zero_iff_nil in H1; subst. simpl in *.
  destruct b2. inv Heql2. inv Heql2. repeat rewrite app_nil_r. constructor; easy.
  simpl in *. inv Heql1.
  destruct b1. simpl in *. lia. simpl in *. inv Heql2.
  assert (env_state_eq (((s, t) :: a1) ++ a2) (((s, a) :: b1) ++ b2)). simpl.
  apply env_state_eq_many; try easy.
  apply env_state_eq_same_length in H2 as X1; try easy.
  apply env_state_eq_app_join; try easy.
Qed.

(*
Lemma find_env_ch: forall T s s' t, find_env T s (Some (s',t)) -> (exists T', env_equiv T T' /\ find_env T' s (Some (s',CH))).
Proof.
 intros. remember (Some (s',t)) as a. induction H; subst. inv Heqa.
 inv Heqa.
 exists ((s',CH)::S).
 split. apply env_subtype.
 destruct t; constructor.
 constructor. easy.
 assert (Some (s', t) = Some (s', t)) by easy. apply IHfind_env in H1.
 destruct H1 as [T' [X1 X2]].
 exists ((x,v)::T').
 split.
 constructor. easy.
 apply find_env_many_2. easy. easy.
Qed.

Lemma find_type_ch : forall T1 s s' t, find_type T1 s (Some (s',t)) -> find_type T1 s (Some (s',CH)).
Proof.
  intros. inv H.
  specialize (find_env_ch S' s s' t H1) as X1. destruct X1 as [T' [X1 X2]].
  apply find_type_rule with (S := T1) in X2; try easy.
  apply env_equiv_trans with (T2 := S'); easy.
Qed.
*)

Lemma pick_mea_exists {rmax:nat}: forall S l m b x n, @qstate_wt ((((x,BNum 0,BNum n)::l, Cval m b)::S)) ->
          exists r v, @pick_mea n (Cval m b) (r,v).
Proof.
  intros.
  unfold qstate_wt in *.
  specialize (H ((x, BNum 0, BNum n) :: l) m b).
  assert (In ((x, BNum 0, BNum n) :: l, Cval m b)
      (((x, BNum 0, BNum n) :: l, Cval m b) :: S)). simpl in *.
  left. easy. apply H in H0.
  assert (exists i, 0 <= i < m). exists 0. lia. destruct H1.
  remember (b x0) as ra. destruct ra.
  exists (Cmod c). exists (a_nat2fb r n).
  apply pick_meas with (i := x0); try easy.
Qed. 


Axiom mask_state_exists: forall n m bl r v,
             @pick_mea n (Cval m bl) (r,v) ->
          (exists na p, build_state_ch n v (Cval m bl) = Some (Cval na p) /\ na > 0).

Definition kind_env_wf (env:aenv) : Prop :=
  forall x n, AEnv.MapsTo x (QT n) env -> n > 0.

Definition env_wf (env:type_map) : Prop :=
   forall x t, In (x,t) env -> simple_ses x.

Lemma qstate_wt_app_l: forall s s1, qstate_wt (s++s1) -> qstate_wt s.
Proof.
  intros. unfold qstate_wt in *. intros.
  eapply H. apply in_app_iff. left. apply H0.
Qed.

Lemma qstate_wt_app_r: forall s s1, qstate_wt (s++s1) -> qstate_wt s1.
Proof.
  intros. unfold qstate_wt in *. intros.
  eapply H. apply in_app_iff. right. apply H0.
Qed.

Lemma qstate_wt_app: forall s s1, qstate_wt s -> qstate_wt s1 -> qstate_wt (s++s1).
Proof.
  induction s; intros; simpl in *; try easy.
  unfold qstate_wt. intros. simpl in *. destruct H1; subst.
  eapply H. simpl. left. easy.
  apply IHs in H0.  apply H0 in H1. easy.
  unfold qstate_wt. intros. eapply H. simpl. right. apply H2.
Qed.


Lemma simple_ses_app_l: forall l l', simple_ses (l++l') -> simple_ses l.
Proof.
  intros. induction l; try easy. constructor.
  inv H. constructor; try easy. apply IHl. easy.
Qed.

Lemma simple_ses_app_r: forall l l', simple_ses (l++l') -> simple_ses l'.
Proof.
  intros. induction l; try easy. 
  simpl in *. inv H. apply IHl. easy.
Qed.

Lemma simple_ses_subst: forall s x v, simple_ses s -> (subst_locus s x v) = s.
Proof.
  induction s; intros;simpl in *; try easy.
  inv H. rewrite IHs; try easy.
  unfold subst_range in *.
  unfold simple_bound in *. destruct x0 eqn:eq1. easy.
  destruct y eqn:eq2. easy.
  unfold subst_bound. easy.
Qed.

Lemma simple_env_subst: forall T x v, simple_tenv T -> (subst_type_map T x v) = T.
Proof.
  induction T; intros; simpl in *; try easy.
  unfold simple_tenv in *. intros. destruct a.
  rewrite IHT. simpl in *.
  rewrite simple_ses_subst. easy.
  specialize (H l s). apply H. left. easy.
  intros. eapply H. simpl. right. apply H0.
Qed.

Lemma aenv_find_add {A:Type}: forall k v (m:AEnv.t A),
        AEnv.find k (AEnv.add k v m) = Some v.
Proof.
      intros.
      apply AEnv.find_1.
      apply AEnv.add_1.
      easy.
Qed.

Lemma aenv_mapsto_add1 {A:Type}: forall k v1 v2 (s:AEnv.t A),
        AEnv.MapsTo k v1 (AEnv.add k v2 s) -> v1 = v2.
Proof.
      intros.
      apply AEnv.find_1 in H.
      rewrite aenv_find_add in H.
      inversion H.
      reflexivity.
Qed.

Lemma aenv_mapsto_always_same {A:Type} : forall k v1 v2 (s:AEnv.t A),
           AEnv.MapsTo k v1 s ->
            AEnv.MapsTo k v2 s -> 
                       v1 = v2.
Proof.
     intros.
     apply AEnv.find_1 in H.
     apply AEnv.find_1 in H0.
     rewrite H in H0.
     injection H0.
     easy.
Qed.

Lemma aenv_mapsto_equal {A:Type} : forall k v (s1 s2:AEnv.t A),
           AEnv.Equal s1 s2 -> AEnv.MapsTo k v s1 ->
            AEnv.MapsTo k v s2.
Proof.
     intros.
     specialize (AEnvFacts.Equal_mapsto_iff s1 s2) as X1.
     destruct X1.
     apply H1 with (k := k) (e := v) in H.
     apply H in H0. easy.
Qed.

(*
Lemma kind_env_stack_equal: forall env s1 s2, AEnv.Equal s1 s2 -> kind_env_stack env s1 -> kind_env_stack env s2.
Proof.
  intros. unfold kind_env_stack in *.
  intros. split; intros.
  apply H0 in H1. destruct H1.
  apply aenv_mapsto_equal with (s4 := s2) in H1; try easy.
  exists x0. easy.
  destruct H1.
  apply H0.
  apply AEnvFacts.Equal_sym in H.
  apply aenv_mapsto_equal with (s4 := s1) in H1; try easy.
  exists x0. easy.
Qed.
*)

Lemma type_cbexp_class: forall env b t, type_cbexp env b t -> t = CT.
Proof.
  intros. induction H; try easy.
Qed.

(*We assume a subset of allowed bexp syntax. *)
Axiom eval_bexp_exists : forall aenv n b s l l1 m f, type_bexp aenv b (QT n, l) 
   -> exists f', @eval_bexp ((l++l1, Cval m f)::s) b ((l++l1, Cval m f')::s).

Lemma type_bexp_gt : forall env b n l, type_bexp env b (QT n, l) -> n > 0.
Proof.
  intros. remember (QT n, l) as t. induction H; try easy.
  inv Heqt.
  apply type_cbexp_class in H. inv H. inv Heqt. lia.
  inv Heqt. lia. inv Heqt. lia. inv Heqt. lia. inv Heqt. lia.
  subst. apply IHtype_bexp. easy.
Qed.

Lemma union_f_same: forall t t1 t2 t3, union_f t t1 t2 -> union_f t t1 t3 -> t2 = t3.
Proof.
  intros. generalize dependent t3.
  induction H; intros; subst;try easy.
  inv H0. easy. inv H0. easy.
  inv H0. easy. inv H0. easy. 
Qed.

Lemma type_aexp_only: forall env b t t', type_aexp env b t
         -> type_aexp env b t' -> t = t'.
Proof.
  intros. generalize dependent t'.
  induction H; intros;subst. inv H0. easy.
  apply aenv_mapsto_always_same with (v1 := CT) in H3; try easy; subst.
  inv H0.
  apply aenv_mapsto_always_same with (v1 := QT n) in H3; try easy; subst.
  apply aenv_mapsto_always_same with (v1 := QT n) in H3; try easy; subst.
  inv H3. easy.
  inv H0. easy.
  inv H2.
  apply IHtype_aexp1 in H5.
  apply IHtype_aexp2 in H7. subst.
  apply union_f_same with (t2 := t3) in H9; subst;try easy.
  inv H2.
  apply IHtype_aexp1 in H5.
  apply IHtype_aexp2 in H7. subst.
  apply union_f_same with (t2 := t3) in H9; subst;try easy.
Qed.

Lemma type_cbexp_only: forall env b t t', type_cbexp env b t
         -> type_cbexp env b t' -> t = t'.
Proof.
  intros. induction H. inv H0.
  apply type_aexp_only with (t := (CT, nil)) in H; subst; try easy.
  inv H0.
  apply type_aexp_only with (t := (CT, nil)) in H; subst; try easy.
Qed.

Lemma type_bexp_only: forall env b t t', type_bexp env b t
         -> type_bexp env b t' -> t = t'.
Proof.
  intros. induction H. inv H0.
  apply type_cbexp_only with (t := t0) in H; subst; try easy.
  inv H0.
  apply aenv_mapsto_always_same 
      with (v1 := (QT m0)) in H; try easy; subst.
  apply aenv_mapsto_always_same 
      with (v1 := (QT n0)) in H1; try easy; subst.
  inv H. inv H1. easy.
  inv H0.
  apply aenv_mapsto_always_same 
      with (v1 := (QT m0)) in H; try easy; subst.
  apply aenv_mapsto_always_same 
      with (v1 := (QT n0)) in H1; try easy; subst.
  inv H. inv H1. easy.
  inv H0.
  apply aenv_mapsto_always_same 
      with (v1 := (QT m0)) in H; try easy; subst.
  apply aenv_mapsto_always_same 
      with (v1 := (QT n0)) in H1; try easy; subst.
  inv H. inv H1. easy.
  inv H0.
  apply aenv_mapsto_always_same 
      with (v1 := (QT m0)) in H; try easy; subst.
  apply aenv_mapsto_always_same 
      with (v1 := (QT n0)) in H1; try easy; subst.
  inv H. inv H1. easy.
  inv H0. easy.
  inv H0.
  apply IHtype_bexp. easy.
Qed.

Axiom fun_all_equal : forall (f c: rz_val), f = c \/ f <> c.

Lemma find_basis_elems_exists: forall n n' f fc i, exists m acc, find_basis_elems n n' f fc i m acc.
Proof.
  induction i;intros;simpl in *.
  exists 0, (fun _ => (C0,allfalse)). apply find_basis_empty.
  destruct IHi as [m [acc H]].
  assert (f = cut_n (lshift_fun (snd (fc i)) n') n \/ f <> cut_n (lshift_fun (snd (fc i)) n') n) by apply classic.
  destruct H0.
  exists (S m),(update acc m (fc i)). constructor; try easy.
  exists m,acc. constructor; try easy.
Qed.

Lemma assem_bool_exists: forall n n' i m f fc, exists mv fv, assem_bool n n' i f (Cval m fc) (Cval mv fv).
Proof.
  induction i;intros;simpl in *.
  exists 0, (fun _ => (C0,allfalse)). apply assem_bool_empty.
  destruct (IHi m f fc) as [m' [acc H]].
  destruct (find_basis_elems_exists n n' (cut_n (snd (f i)) n) fc m) as [mv [fv H1]].
  destruct mv.
  exists (S m'), ((update acc m' (f i))).
  eapply assem_bool_many_1; try easy. apply H1.
  destruct (assem_list (S mv) m' n (cut_n (snd (f i)) n) fv acc) eqn:eq1.
  exists n0,p.
  eapply assem_bool_many_2 with (mv := (S mv)); try easy. apply H. lia. apply H1. easy.
Qed.

Lemma simple_subst_ses: forall s i l, simple_ses (subst_locus s i l) -> (forall v, simple_ses (subst_locus s i v)).
Proof.
  intros.
  induction s. simpl in *. easy.
  simpl in *. inv H.
  unfold subst_range in *. destruct a. destruct p. inv H0.
  constructor.
  unfold simple_bound in *.
  unfold subst_bound in *.
  destruct b0. bdestruct (i =? v1); easy. easy.
  unfold simple_bound,subst_bound in *.
  destruct b. bdestruct (i =? v1); easy. easy.
  apply IHs. easy.
Qed.

Lemma simple_tenv_subst_right: forall T i l,
  simple_tenv (subst_type_map T i l) -> (forall v, simple_tenv (subst_type_map T i v)).
Proof.
  intros. unfold simple_tenv in *.
  intros. induction T; simpl in *. easy.
  destruct a0. simpl in *. destruct H0. inv H0.
  specialize (H (subst_locus l0 i l) b). 
  assert ((subst_locus l0 i l, b) = (subst_locus l0 i l, b) \/
    In (subst_locus l0 i l, b) (subst_type_map T i l)). left. easy.
  apply H in H0. eapply simple_subst_ses. apply H0.
  apply IHT. intros. apply H with (b := b0). right. easy.
  easy.
Qed.


Lemma simple_tenv_app_l: forall T T1, simple_tenv (T++T1) -> simple_tenv T.
Proof.
  intros. unfold simple_tenv in *; intros. eapply H.
  apply in_app_iff. left. apply H0.
Qed.

Lemma simple_tenv_app_r: forall T T1, simple_tenv (T++T1) -> simple_tenv T1.
Proof.
  intros. unfold simple_tenv in *; intros. eapply H.
  apply in_app_iff. right. apply H0.
Qed.

Lemma simple_tenv_app: forall T T1, simple_tenv T -> simple_tenv T1 -> simple_tenv (T++T1).
Proof.
  intros. unfold simple_tenv in *; intros.
  apply in_app_iff in H1. destruct H1. eapply H. apply H1.
  eapply H0. apply H1.
Qed.

Lemma bexp_extend: forall aenv b n l l1 v v' s sa, type_bexp aenv b (QT n, l) ->
      eval_bexp ((l ++ l1, v) :: s) b ((l ++ l1, v') :: s) ->
      eval_bexp ((l ++ l1, v) :: s++sa) b ((l ++ l1, v') :: s++sa).
Proof.
  intros. remember ((l ++ l1, v) :: s) as S1. remember ((l ++ l1, v') :: s) as S2.
  induction H0; simpl in *; subst; try easy. inv HeqS1. inv HeqS2.
  apply beq_sem_1. easy.
  inv HeqS1. inv HeqS2.
  apply beq_sem_2. easy.
  inv HeqS1. inv HeqS2.
  apply blt_sem_1. easy.
  inv HeqS1. inv HeqS2.
  apply blt_sem_2. easy.
Qed.

Lemma bexp_extend_1: forall aenv b n l l1 v v' s, type_bexp aenv b (QT n, l) ->
      eval_bexp ((l ++ l1, v) :: s) b ((l ++ l1, v') :: s) ->
      eval_bexp ((l ++ l1, v) :: nil) b ((l ++ l1, v') :: nil).
Proof.
  intros. remember ((l ++ l1, v) :: s) as S1. remember ((l ++ l1, v') :: s) as S2.
  induction H0; simpl in *; subst; try easy. inv HeqS1. inv HeqS2.
  apply beq_sem_1. easy.
  inv HeqS1. inv HeqS2.
  apply beq_sem_2. easy.
  inv HeqS1. inv HeqS2.
  apply blt_sem_1. easy.
  inv HeqS1. inv HeqS2.
  apply blt_sem_2. easy.
Qed.


Lemma state_equiv_local : forall rmax s sa s1, @state_equiv rmax s sa -> @state_equiv rmax (s++s1) (sa++s1).
Proof.
  intros. induction H; intros; simpl in *; try easy.
  constructor. apply state_sub with (n0 := n); try easy.
  apply state_mut with (n0 := n) (n3 := n1) (n4 := n2); try easy.
  apply state_cong. easy.
Qed.

Lemma step_sem_local: forall rmax aenv s e r s' e' s1,
   @step rmax aenv s e r s' e' -> @step rmax aenv (s++s1) e r (s'++s1) e'.
Proof.
  intros. induction H; simpl in *; try easy.
  constructor.
  constructor. easy.
  apply let_step_q with (n0 := n); try easy.
  constructor. easy.
  constructor. easy.
  constructor; easy.
  constructor; easy.
  constructor; easy.
  constructor; easy.
  constructor; easy.
  constructor; easy.
  constructor; easy.
  apply if_sem_q with (n0 := n) (fc0 := fc) (fc'0 := fc'); try easy.
  apply if_sem_side with (n0 := n); try easy.
  apply bexp_extend with (aenv := aenv) (n := n); try easy.
  constructor; easy.
  constructor; easy.
Qed.

Lemma simple_ses_comm: forall l1 l2, simple_ses (l1 ++ l2) -> simple_ses (l2 ++ l1).
Proof.
  induction l1; intros; simpl in *; try easy. rewrite app_nil_r. easy.
  simpl in *. inv H. simpl in *. apply IHl1 in H4.
  induction l2; intros; simpl in *; try easy.
  constructor; try easy.
  inv H4. apply IHl2 in H6. constructor; try easy.
Qed.

Lemma simple_ses_swap: forall l1 l2 x y, simple_ses (l1 ++ x :: y :: l2)
   -> simple_ses (l1 ++ y :: x :: l2).
Proof.
  induction l1; intros; simpl in *; try easy.
  inv H. inv H4. constructor; try easy. constructor; try easy.
  inv H. constructor; try easy. apply IHl1. assumption.
Qed.

Lemma env_equiv_simple: forall T T1, env_equiv T T1 -> simple_tenv T -> simple_tenv T1.
Proof.
  intros. induction H; try easy.
  unfold simple_tenv in *. intros. simpl in *.
  destruct H1; try easy.
  inv H1.
  assert ((a, v) = (a, v) \/ In (a, v) S).
  left. easy. apply H0 in H1. easy. eapply H0. right. apply H1.
  unfold simple_tenv in *.
  intros.
  simpl in *. destruct H; try easy.
  inv H.
  assert ((l1 ++ x :: y :: l2, b) = (l1 ++ x :: y :: l2, b) 
         \/ In (l1 ++ x :: y :: l2, b) S).
  left. easy. apply H0 in H.
  apply simple_ses_swap. easy.
  eapply H0. right. apply H.
  assert (simple_tenv T1).
  unfold simple_tenv in *. intros. eapply H0. simpl. right. apply H1.
  apply IHenv_equiv in H1.
  unfold simple_tenv in *. intros. simpl in *.
  destruct H2; subst; try easy.
  assert ((a, b) = (a, b) \/ In (a, b) T1).
  left. easy. apply H0 in H2.
  easy. eapply H1. apply H2.
Qed.

Lemma perm_envs_simple: forall T T1, perm_envs T T1 -> simple_tenv T -> simple_tenv T1.
Proof.
  intros. induction H. easy.
  apply IHperm_envs. inv H.
  unfold simple_tenv in *.
  simpl in *. intros. destruct H; try easy.
  inv H.
  assert ((l1 ++ x :: y :: l2, b) = (l1 ++ x :: y :: l2, b) \/ In (l1 ++ x :: y :: l2, b) S).
  left. easy. apply H0 in H. apply simple_ses_swap. easy.
  eapply H0. right. apply H.
Qed.

Lemma simple_tenv_ses_system: forall rmax t aenv T e T',
  simple_tenv T -> @locus_system rmax t aenv T e T' -> simple_tenv T'.
Proof.
  intros. induction H0; simpl in *; try easy.
  apply env_equiv_simple with (T := T'). easy. apply IHlocus_system. easy.
  apply simple_tenv_app_l in H as X1.
  apply simple_tenv_app_r in H as X2.
  apply simple_tenv_app; try easy. apply IHlocus_system. easy.
  apply IHlocus_system. easy.
  apply IHlocus_system; try easy.
  unfold simple_tenv in *.
  intros. simpl in *. destruct H3. inv H3.
  specialize (H ((y, BNum 0, BNum n) :: a) CH).
  assert (((y, BNum 0, BNum n) :: a, CH) = ((y, BNum 0, BNum n) :: a, CH) \/
    In ((y, BNum 0, BNum n) :: a, CH) T ). left. easy.
  apply H in H3. inv H3. easy. eapply H. right. apply H3.
  unfold simple_tenv in *. intros. simpl in *. destruct H2; try easy.
  inv H2. eapply H. left. easy.
  unfold simple_tenv in *. intros. simpl in *. destruct H2; try easy.
  inv H2. eapply H. left. easy.
  apply IHlocus_system2; try easy.
  apply IHlocus_system1; try easy.
  apply simple_tenv_subst_right with (v := h) in H. easy.
Qed.

Lemma freeVarsAExpSimple: forall env a, 
     freeVarsNotCAExp env a -> type_aexp env a (CT, nil) -> exists v, simp_aexp a = Some v.
Proof.
  intros. remember (CT,nil) as t. induction H0; simpl in *.
  apply H in H0. easy.
  simpl. left. easy. inv Heqt. 
  exists n. easy.
  assert (freeVarsNotCAExp env e1).
  unfold freeVarsNotCAExp in *. simpl in *.
  intros. eapply H. apply in_app_iff. left. apply H1. easy.
  apply IHtype_aexp1 in H1; try easy.
  destruct H1. rewrite H1 in *.
  assert (freeVarsNotCAExp env e2).
  unfold freeVarsNotCAExp in *. simpl in *.
  intros. eapply H. apply in_app_iff. right. apply H2. easy.
  apply IHtype_aexp2 in H2; try easy.
  destruct H2. rewrite H2 in *. exists (x+x0). easy. rewrite Heqt in *.
  inv H0. easy. rewrite Heqt in *. inv H0. easy.
  subst.
  assert (freeVarsNotCAExp env e1).
  unfold freeVarsNotCAExp in *. simpl in *.
  intros. eapply H. apply in_app_iff. left. apply H1. easy.
  apply IHtype_aexp1 in H1; try easy.
  destruct H1. rewrite H1 in *.
  assert (freeVarsNotCAExp env e2).
  unfold freeVarsNotCAExp in *. simpl in *.
  intros. eapply H. apply in_app_iff. right. apply H2. easy.
  apply IHtype_aexp2 in H2; try easy.
  destruct H2. rewrite H2 in *. exists (x*x0). easy.
  inv H0. easy. inv H0. easy.
Qed.

Lemma freeVarsCBExpSimple: forall env b, 
     freeVarsNotCBExp env (CB b) -> type_cbexp env b CT -> exists v, simp_bexp (CB b) = Some v.
Proof.
  intros. inv H0. unfold freeVarsNotCBExp in *.
  simpl in *.
  assert (exists v1, simp_aexp a = Some v1).
  apply (freeVarsAExpSimple env); try easy.
  unfold freeVarsNotCAExp. intros.
  eapply H. apply in_app_iff. left. apply H0. apply H3.
  assert (exists v2, simp_aexp b0 = Some v2).
  apply (freeVarsAExpSimple env); try easy.
  unfold freeVarsNotCAExp. intros.
  eapply H. apply in_app_iff. right. apply H3. apply H4.
  destruct H0. destruct H3.
  rewrite H0. rewrite H3. exists (x =? x0). easy.
  unfold freeVarsNotCBExp in *.
  simpl in *.
  assert (exists v1, simp_aexp a = Some v1).
  apply (freeVarsAExpSimple env); try easy.
  unfold freeVarsNotCAExp. intros.
  eapply H. apply in_app_iff. left. apply H0. apply H3.
  assert (exists v2, simp_aexp b0 = Some v2).
  apply (freeVarsAExpSimple env); try easy.
  unfold freeVarsNotCAExp. intros.
  eapply H. apply in_app_iff. right. apply H3. apply H4.
  destruct H0. destruct H3.
  rewrite H0. rewrite H3. exists (x <? x0). easy.
Qed.

Lemma freeVarsBExpSimple: forall env b, 
     freeVarsNotCBExp env b -> type_bexp env b (CT, nil) -> exists v, simp_bexp b = Some v.
Proof.
  intros. remember (CT,nil) as t. induction H0.
  apply (freeVarsCBExpSimple env); try easy. inv Heqt. easy.
  1-5:inv Heqt. 
  subst.
  assert (freeVarsNotCBExp env b).
  unfold freeVarsNotCBExp in *.
  intros. eapply H. simpl in *. apply H1. easy.
  apply IHtype_bexp in H1; try easy. destruct H1.
  exists (negb x). simpl. rewrite H1. easy.
Qed.

Definition btest_or (b:bexp) :=
   match b with BTest  i e  => True | _ => False end.

Lemma qm_step_prob_1: forall rmax env T e T' s r s' e',
   @locus_system rmax QM env T e T' -> @step rmax env s e r s' e' -> r = R1.
Proof.
  intros. remember QM as c. 
  generalize dependent s'. 
  generalize dependent e'. 
  induction H; intros; subst; try easy.
  apply IHlocus_system with (e' := e') (s' := s'); try easy.
  apply IHlocus_system with (e' := e') (s' := s'); try easy. inv H0. easy.
  inv H2. easy. inv H1; easy. inv H1; easy.
  inv H1; easy. inv H1; easy. inv H1; try easy. inv H1; try easy.
  inv H1; try easy.
  inv H1; try easy. eapply IHlocus_system1; try easy. apply H9.
  inv H0; try easy. inv H3; try easy.
Qed.


Lemma type_qm_no_meas: forall rmax aenv T e T', @locus_system rmax QM aenv T e T' ->
   (forall x a ea, e <> Let x (Meas a) ea).
Proof.
  intros. remember QM as t.
  induction H; subst; try easy.
  apply IHlocus_system; try easy.
  apply IHlocus_system; try easy.
Qed.

Lemma locus_system_same_length: forall rmax a env e T Ta,
   @locus_system rmax a env T e Ta -> length T = length Ta.
Proof.
  intros. induction H; try easy.
  apply equiv_env_same_length in H0. rewrite IHlocus_system. easy.
  repeat rewrite app_length.
  rewrite IHlocus_system. easy.
  rewrite IHlocus_system1. rewrite IHlocus_system2. easy.
  rewrite length_subst with (v := h). easy.
Qed.


Lemma locus_system_qm_single_same: forall rmax env e T Ta,
   is_cval_t T -> length T <= 1 -> @locus_system rmax QM env T e Ta -> env_equiv T Ta.
Proof.
  intros. remember QM as a.
  induction H1; subst; intros; try easy.
  apply env_trans with (T2 := T'); try easy. apply IHlocus_system; try easy.
  destruct T; try easy. simpl in *.
  assert (env_equiv nil T'). apply IHlocus_system; try easy. lia.
  inv H2. simpl in *. constructor.
  simpl in *. destruct p.
  assert (length (T ++ T1) = 0) by lia.
  apply length_zero_iff_nil in H2.
  apply app_eq_nil in H2. destruct H2; subst. simpl in *.
  destruct s0;try easy. rewrite app_nil_r. apply IHlocus_system; try easy. constructor.
  apply IHlocus_system; try easy.
  1-4:constructor.
  apply env_trans with (T2 := T1). apply IHlocus_system1; try easy.
  assert (env_equiv T T1). apply IHlocus_system1; try easy.
  apply env_equiv_single_prog in H1; try easy. destruct H1.
  apply IHlocus_system2; try easy.
  rewrite <- H2 in H0. easy. constructor.
  clear H3.
  assert (forall v,is_cval_t (subst_type_map T i v)).
  apply is_cval_t_subst with (a := l). easy.
  assert (forall v, length (subst_type_map T i v) <= 1).
  intros. rewrite <- length_subst with (a := l); try easy.
  clear H H0 H2.
  assert (exists v, h = l + v). exists (h-l). lia.
  destruct H. subst.
  induction x. lia.
  destruct x. simpl in *.
  assert (l <= l < l + 1) by lia.
  apply H4 in H; try easy.
  assert (l <= l + S x < l + S (S x)) by lia.
  apply H4 in H; try easy.
  replace (l+ S x + 1) with (l + S (S x)) in H by lia.
  apply env_trans with (T2 := (subst_type_map T i (l + S x))); try easy.
  apply IHx; try easy.
  intros. apply H4; try easy. lia. lia.
Qed.

Lemma simple_env_same_state: forall rmax aenv l s r e s' e',
  simple_ses l -> @locus_system rmax QM aenv ([(l,CH)]) e ([(l,CH)]) -> @step rmax aenv s e r s' e'
   -> env_state_eq ([(l,CH)]) s -> env_state_eq ([(l,CH)]) s'.
Proof.
(*
  intros. induction H1; simpl in *; try easy.
  apply type_qm_no_meas with (x := x) (a := a) (ea := e) in H0; try easy.
  inv H2. inv H5. inv H10. inv H2. inv H5. inv H10. repeat constructor.
  inv H2. inv H10. inv H2. inv H10.
*)
Admitted.

Lemma subtype_env_state: forall rmax n t t' v, subtype t t' -> type_state_elem_same t v
   -> exists u, @state_same rmax n v u /\ type_state_elem_same t' u.
Proof.
  intros. inv H. exists v. split. constructor.
  easy. inv H0. exists ((Cval 1 (fun i => if i =? 0 then (p,r) else (C0,allfalse)))).
  split. apply nor_ch_ssame. constructor.
  inv H0. exists ((Cval (2^n) (sum_rotates n rmax bl))).
  split. constructor. constructor.
Qed.

Lemma ses_len_cons: forall x l n, ses_len (x::l) = Some n ->
        exists na, ses_len ([x]) = Some na /\ ses_len l = Some (n-na) /\ na <= n.
Proof.
  intros. unfold ses_len in *.
  simpl in *. destruct x; try easy. destruct p; try easy.
  destruct b0; try easy. destruct b; try easy.
  destruct (get_core_ses l) eqn:eq1. simpl in *.
  inv H. exists (n1-n0+0). split;try easy.
  split. assert ((ses_len_aux l0) = (n1 - n0 + ses_len_aux l0 - (n1 - n0 + 0))) by lia.
  rewrite <- H. easy. lia.
  easy.
Qed.


Lemma state_equiv_length_same: forall rmax s sa, @state_equiv rmax s sa 
      -> length s = length sa.
Proof.
  intros. induction H; try easy. simpl.
  rewrite IHstate_equiv. easy.
Qed.

(*
Lemma state_equiv_tl: forall rmax a b l l1, @state_equiv rmax (a::l) (b::l1) -> @state_equiv rmax l l1.
Proof.
  intros. inv H. constructor. constructor. constructor. constructor. easy.
Qed.

Lemma state_equiv_hd: forall rmax a b l l1, @state_equiv rmax (a::l) (b::l1) -> @state_equiv rmax ([a]) ([b]).
Proof.
  intros. remember (a::l) as L1. remember (b::l1) as L2.
  generalize dependent a. generalize dependent b. generalize dependent l. generalize dependent l1.
  induction H; intros; simpl in *; try easy. destruct S. easy. inv HeqL1. inv HeqL2. constructor.
  inv HeqL1. inv HeqL2. eapply state_sub. apply H.
  easy. inv HeqL1. inv HeqL2. eapply state_mut. apply H. apply H0. apply H1. easy. easy.
  inv HeqL1. inv HeqL2.
  assert (s2 :: l1 = s2 :: l1) by easy.
  assert (a :: l1 = a :: l1) by easy.
  specialize (IHstate_equiv1 l1 l1 s2 H1 a H2).
  assert (b :: l1 = b :: l1) by easy.
  specialize (IHstate_equiv2 l1 l1 b H3 s2 H1).
  apply state_trans with (s3 := s2); try easy.
  inv HeqL1. inv HeqL2. constructor.
Qed.
*)

Lemma env_equiv_state_eq: forall rmax T T1 s, simple_tenv T -> env_equiv T T1 ->
       env_state_eq T s -> exists s1, @state_equiv rmax s s1 /\ env_state_eq T1 s1.
Proof.
  intros. generalize dependent s. induction H0; intros; simpl in *.
  exists s. split. apply state_id. easy.
  inv H1. assert (simple_ses s). eapply H. simpl. left. easy.
  apply ses_len_simple in H1 as X1. destruct X1 as [n X1].
  apply subtype_env_state with (rmax := rmax) (n := n) (t':= v') in H7 as X2; try easy.
  destruct X2 as [u [X2 X3]].
  exists ((s, u) :: l2). split.
  apply state_sub with (n0 := n); try easy.
  constructor; try easy.
  inv H1.
  assert (simple_ses (l1 ++ x :: y :: l2)) as X1.
  eapply H. simpl. left. easy.
  apply simple_ses_swap in X1 as X2.
  apply simple_ses_app_l in X1 as X3.
  apply simple_ses_app_r in X1 as X4.
  apply ses_len_simple in X3 as X5; try easy.
  apply ses_len_simple in X4 as X6; try easy.
  destruct X5 as [n X5].
  destruct X6 as [n1 X6].
  apply ses_len_cons in X6 as X7.
  destruct X7 as [na [X7 [X8 X9]]].
  apply ses_len_cons in X8 as X10.
  destruct X10 as [nb [X10 [X11 X12]]].
  assert (exists u, mut_state n na nb a u /\ type_state_elem_same v u).
  inv H6. exists (Nval p (mut_nor_aux n na nb r)). split. constructor. constructor.
  exists (Hval (mut_had_state n na nb bl)). split. constructor. constructor.
  exists (Cval m (mut_fch_state n na nb bl)). split; constructor.
  destruct H0 as [u [X13 X14]].
  exists (((l1 ++ y :: x :: l2), u) :: l3).
  split. apply state_mut with (n0 := n) (n2 := na) (n3 := nb); try easy.
  constructor; try easy.
  inv H1. apply IHenv_equiv in H4 as X1.
  destruct X1 as [sa [X1 X2]].
  exists ((s0,a)::sa). split. apply state_cong. easy.
  constructor; try easy.
  unfold simple_tenv in *.
  intros; eapply H. simpl. right. apply H1.
Qed.

Lemma state_equiv_qstate_wt : forall rmax s s1, @state_equiv rmax s s1 -> qstate_wt s -> qstate_wt s1.
Proof.
  intros. induction H; simpl in *; try easy.
  unfold qstate_wt in *. intros. simpl in *. destruct H2; try easy.
  inv H2. inv H1. eapply H0. left. easy. lia. assert (2^n <> 0).
  apply Nat.pow_nonzero; try lia. lia.
  eapply H0. right. apply H2.
  unfold qstate_wt in *. simpl in *. intros. destruct H4.
  inv H4. inv H3. eapply H0. left. easy.
  eapply H0. right. apply H4.
  assert (qstate_wt S1).
  unfold qstate_wt in *. intros. eapply H0. right. apply H1.
  apply IHstate_equiv in H1.
  unfold qstate_wt in *. intros.
  simpl in *. destruct H2; subst.
  eapply H0. left. easy.
  eapply H1. apply H2.
Qed.

Lemma env_equiv_app: forall T1 T T2, env_equiv T (T1++T2) 
       -> exists Ta Tb, T = Ta++Tb /\ env_equiv Ta T1 /\ env_equiv Tb T2.
Proof.
  intros. remember (T1++T2) as A.
  generalize dependent T1.
  generalize dependent T2.
  induction H; subst; intros; simpl in *; try easy.
  exists T1,T2. split; try easy. split; constructor.
  destruct T1; try easy. destruct T2; try easy. simpl in *. inv HeqA.
  exists nil, ((s, v) :: T2). split; try easy. split; try constructor. easy.
  inv HeqA.
  exists ((s, v) :: T1), T2. split;try easy.
  split. apply env_subtype; try easy. constructor.
  destruct T1; try easy. simpl in *. rewrite <- HeqA in *. clear HeqA.
  exists nil, ((l1 ++ x :: y :: l2, v) :: S).
  split. easy. split; try constructor.
  inv HeqA.
  exists ((l1 ++ x :: y :: l2, v) :: T1), T2.
  split; try easy.
  split. apply env_mut. constructor. 
  destruct T3; try easy. simpl in *.
  subst. exists nil, (x::T1). split; try easy.
  split. constructor. apply env_cong. easy.
  simpl in *. inv HeqA.
  assert (T3 ++ T0 = T3 ++ T0) by easy.
  destruct (IHenv_equiv T0 T3 H0) as [Ta [Tb [X1 [X2 X3]]]].
  exists (p::Ta),Tb. simpl in *. subst. split; try easy.
  split. apply env_cong. easy. easy.
Qed.

Lemma state_equiv_empty: forall rmax s1, @state_equiv rmax nil s1 -> s1 = nil.
Proof.
  intros. remember nil as a. induction H; subst; try easy.
(*
  assert (S2 = nil). apply IHstate_equiv1. easy. subst. apply IHstate_equiv2. easy.
*)
Qed.

Lemma state_equiv_empty_r: forall rmax s1, @state_equiv rmax s1 nil -> s1 = nil.
Proof.
  intros. remember nil as a. induction H; subst; try easy.
(*
  assert (S2 = nil). apply IHstate_equiv2. easy. subst. apply IHstate_equiv1. easy.
*)
Qed.

Lemma env_equiv_empty: forall s1, env_equiv nil s1 -> s1 = nil.
Proof.
  intros. remember nil as a. induction H; subst; try easy.
(*
  assert (T2 = nil). apply IHenv_equiv1. easy. subst. apply IHenv_equiv2. easy.
*)
Qed.

Lemma env_equiv_empty_r: forall s1, env_equiv s1 nil -> s1 = nil.
Proof.
  intros. remember nil as a. induction H; subst; try easy.
 (* assert (T2 = nil). apply IHenv_equiv2. easy. subst. apply IHenv_equiv1. easy. *)
Qed.

Lemma state_equiv_cong: forall rmax s sa sb, @state_equiv rmax sa sb
   -> @state_equiv rmax (s++sa) (s++sb).
Proof.
  intros. induction s. simpl in *. easy.
  simpl in *. apply state_cong. easy.
Qed.

Lemma state_equiv_cong_1: forall rmax s sa sb, @state_equiv rmax sa sb
   -> @state_equiv rmax (sa++s) (sb++s).
Proof.
  intros. induction H.
  constructor.
  simpl. eapply state_sub. apply H. easy.
  simpl. eapply state_mut. apply H. apply H0. apply H1. easy.
  simpl. apply state_cong. easy.
Qed.

Lemma state_equiv_app: forall rmax s1 s2 sa sb, @state_equiv rmax s1 sa -> @state_equiv rmax s2 sb
       -> @state_equiv rmax (s1++s2) (sa++sb).
Proof.
  intros. induction H. induction S. simpl in *. easy.
  simpl in *. apply state_cong. easy.
  simpl in *.
  apply state_trans with (S2 := ((x, u) :: a ++ s2)).
  apply state_sub with (n0 := n); try easy.
  repeat rewrite app_comm_cons.
  apply state_equiv_cong. easy.
  apply state_trans with (S2 := (((l1 ++ b :: a :: l2, u) :: S) ++ s2)).
  eapply state_mut; try easy. apply H. apply H1. apply H2. easy.
  repeat rewrite app_comm_cons.
  apply state_equiv_cong. easy.
  simpl. apply state_cong. easy.
Qed.

Definition error_fst {A:Type} {B:Type} (l1 l2: option (A * B)) :=
      match (l1,l2) with (Some (a,b), Some (c,d)) => a = c | _ => False end.

Definition error_snd {A:Type} {B:Type} (l1 l2: option (A * B)) :=
      match (l1,l2) with (Some (a,b), Some (c,d)) => b = d | _ => False end.

Definition same_first_var (l1 l2: qstate) :=
     error_fst (hd_error l1) (hd_error l2).

Definition same_snd_val (l1 l2: qstate) :=
     error_snd (hd_error l1) (hd_error l2).

Definition is_cval (l: qstate) := match l with ((x,Cval m b)::l) => True | _ => False end.

Lemma state_equiv_single_eq: forall rmax l m bl v,
       @state_equiv rmax ([(l, Cval m bl)]) ([(l,v)]) -> Cval m bl = v.
Proof.
  intros.
  inv H; try easy.
  inv H5. easy.
  apply app_inv_head_iff in H3. inv H3.
Admitted.

Lemma type_progress : 
    forall e rmax t aenv s tenv T tenv', @env_state_eq tenv s ->
      env_equiv tenv T -> @locus_system rmax t aenv T e tenv' -> freeVarsNotCPExp aenv e
       -> @qstate_wt s -> simple_tenv tenv ->
          (exists sa s' r e', @state_equiv rmax s sa /\ @env_state_eq T sa /\ @step rmax aenv sa e r s' e'
             /\ @qstate_wt s').
Proof.
  intros.
  generalize dependent s.
  generalize dependent tenv.
  induction H1; simpl in *; intros.
 - apply env_equiv_state_eq with (rmax := rmax) (s := s0) in H0 as X1; try easy.
  destruct X1 as [s1 [X1 X2]].
  apply state_equiv_qstate_wt in X1 as X3; try easy.
  apply env_equiv_simple in H0 as X4; try easy.
  assert (env_equiv T T) by constructor.
  destruct (IHlocus_system H2 T H6 X4 s1 X2 X3) as [sa [sb [r [e' [Y1 [Y2 [Y3 Y4]]]]]]].
  exists sa,sb,r,e'. split. eapply state_trans. apply X1. easy.
  split. easy. split. easy. easy.
 - apply env_equiv_app in H0 as X1. destruct X1 as [Ta [Tb [X1 [X2 X3]]]]; subst.
  apply env_state_eq_app in H as X1; try easy.
  destruct X1 as [s1 [s2 [X4 [X5 X6]]]]; subst.
  apply env_state_eq_same_length in X4; try easy.
  destruct X4. apply simple_tenv_app_l in H4 as X4.
  apply qstate_wt_app_l in H3 as X7.
  destruct (IHlocus_system H2 Ta X2 X4 s1 H5 X7) as [sa [s' [r [ea [Y2 [Y3 [Y4 Y5]]]]]]].
  apply simple_tenv_app_r in H4; try easy.
  apply env_equiv_state_eq with (rmax := rmax) (T1 := T1) in H6 as X8; try easy.
  destruct X8 as [s2a [X8 X9]].
  exists (sa++s2a),(s'++s2a),r,ea. split.
  apply state_equiv_app; try easy.
  split.
  apply env_state_eq_app_join; try easy.
  split.
  apply step_sem_local; try easy.
  apply qstate_wt_app; try easy.
  eapply state_equiv_qstate_wt. apply X8.
  apply qstate_wt_app_r in H3. easy.
 - 
  apply env_equiv_empty_r in H0. subst.
  inv H. exists nil,nil,(R1),PSKIP; try easy. split. constructor.
  split. constructor. split. constructor. easy.
 -
  assert (freeVarsNotCAExp env a).
  unfold freeVarsNotCPExp,freeVarsNotCAExp in *.
  intros. eapply H2. simpl. apply in_app_iff. left. apply H7. easy.
  apply freeVarsAExpSimple in H7; try easy. destruct H7 as [v H7]; subst.
  apply env_equiv_state_eq with (rmax := rmax) (s := s) in H3 as X1.
  destruct X1 as [sa [X1 X2]].
  exists sa,sa,R1,(subst_pexp e x v). split; try easy.
  split; try easy. split. constructor. easy.
  eapply state_equiv_qstate_wt. apply X1. 1-3: easy.
 -
  apply env_equiv_state_eq with (rmax := rmax) (s := s) in H3 as X1; try easy.
  destruct X1 as [sa [X1 X2]]. exists sa.
  inv X2. inv H12.
  apply state_equiv_qstate_wt in X1 as X2.
  destruct (@pick_mea_exists rmax l2 (l) m bl y n X2) as [ra [va X3]].
  apply mask_state_exists in X3 as eq1.
  destruct eq1 as [na [p [X4 X5]]].
  exists ((l, (Cval na p)) :: l2),ra,(subst_pexp e x va).
  split. easy. split. constructor; try easy. constructor.
  split. apply let_step_q; try easy.
  unfold qstate_wt in *. intros.
  simpl in *. destruct H7. inv H7. lia.
  eapply X2. right. apply H7. easy.
 -
  apply env_equiv_state_eq with (rmax := rmax) (s := s) in H1 as X1; try easy.
  destruct X1 as [sa [X1 X2]].
  inv X2. inv H11. inv H10.
  apply state_equiv_qstate_wt in X1 as X2; try easy.
  apply env_equiv_simple in H1 as X3; try easy.
  assert (simple_ses (l)).
  unfold simple_tenv in *. eapply X3. simpl. left. easy.
  Check eval_nor_exists.
  destruct (@eval_nor_exists rmax env l n p r e H H6 H0) as [ba X4]. destruct ba.
  exists ([(l, Nval p r)]), ((l,Nval c r0)::nil),R1,PSKIP.
  split. easy. split. constructor. 1-2:constructor.
  split. apply appu_step_nor; try easy.
  unfold qstate_wt in *.
  intros. simpl in *. destruct H7; try easy.
 -
  apply env_equiv_state_eq with (rmax := rmax) (s := s) in H1 as X1; try easy.
  destruct X1 as [sa [X1 X2]].
  inv X2. inv H11. inv H10.
  apply state_equiv_qstate_wt in X1 as X2; try easy.
  apply env_equiv_simple in H1 as X3; try easy.
  assert (simple_ses (l++l')).
  unfold simple_tenv in *. intros.
  eapply X3. simpl. left. easy.
  apply simple_ses_app_l in H6 as X4.
  destruct (@eval_ch_exists rmax m env l n bl e H X4 H0) as [ba X5].
  exists ([(l ++ l', Cval m bl)]), ((l ++ l', Cval m ba) :: nil),R1,PSKIP.
  split. easy. split. constructor. 1-2:constructor.
  split. apply appu_step_ch; try easy. 
  unfold qstate_wt in *.
  intros. simpl in *.
  destruct H7; try easy. inv H7.
  eapply X2. left. easy.
 - 
  apply env_equiv_state_eq with (rmax := rmax) (s := s) in H1 as X1; try easy.
  destruct X1 as [sa [X1 X2]].
  inv X2. inv H11. inv H10.
  apply state_equiv_qstate_wt in X1 as X2; try easy.
  apply env_equiv_simple in H1 as X3; try easy.
  assert (simple_ses ([a])) as X4.
  unfold simple_tenv in *. eapply X3. simpl. left. easy.
  exists ([([a], Nval p0 r)]),
     (([a],(Hval (fun i => (update allfalse 0 (r i)))) )::nil),R1,PSKIP.
  split. easy. split. constructor. 1-2: constructor.
  split. apply appsu_step_h_nor; try easy.
  unfold qstate_wt in *.
  intros. inv H6; try easy.
 -
  apply env_equiv_state_eq with (rmax := rmax) (s := s) in H1 as X1; try easy.
  destruct X1 as [sa [X1 X2]].
  inv X2. inv H11. inv H10.
  apply state_equiv_qstate_wt in X1 as X2; try easy.
  apply env_equiv_simple in H1 as X3; try easy.
  assert (simple_ses ([a])) as X4.
  unfold simple_tenv in *. eapply X3. simpl. left. easy.
  exists ([([a], Hval bl)]),(([a],(Nval C1 (fun j => bl j 0)))::nil),R1,PSKIP.
  split. easy. split. constructor. 1-2:constructor.
  split. apply appsu_step_h_had; try easy.
  unfold qstate_wt in *.
  intros. simpl in *. destruct H6; try easy.
 -
  apply env_equiv_state_eq with (rmax := rmax) (s := s) in H1 as X1; try easy.
  destruct X1 as [sa [X1 X2]].
  inv X2. inv H11. inv H10.
  apply state_equiv_qstate_wt in X1 as X2; try easy.
  apply env_equiv_simple in H1 as X3; try easy.
  assert (simple_ses ([a]++l)).
  unfold simple_tenv in *. intros.
  eapply X3. simpl. left. easy.
  apply simple_ses_app_l in H6 as X4.
  exists ([(a :: l, Cval m0 bl)]), (([a]++l,Cval (m0*2^m) (eval_h_ch m m0 bl)) :: nil),R1,PSKIP.
  split. easy. split. constructor. 1-2:constructor.
  replace (a :: l) with ([a]++l) by easy.
  split. apply appsu_step_h_ch; try easy.
  eapply type_vari_ses_len. apply H. 
  unfold qstate_wt in *.
  intros. simpl in *.
  destruct H7; try easy. inv H7.
  assert ((a :: l, Cval m0 bl) = (a :: l, Cval m0 bl) \/ False ).
  left. easy. apply X2 in H7.
  Check Nat.pow_gt_1.
  assert (2 <> 0) by lia.
  specialize (Nat.pow_nonzero 2 m H8) as A1.
  lia.
 -
  assert (freeVarsNotCBExp env b).
  unfold freeVarsNotCPExp,freeVarsNotCBExp in *.
  intros. eapply H2; simpl in *. apply in_app_iff. left. apply H6. easy.
  apply freeVarsBExpSimple in H6; try easy. destruct H6.
  apply env_equiv_state_eq with (rmax := rmax) (s := s) in H0 as X1; try easy.
  destruct X1 as [sa [X1 X2]].
  destruct x.
  exists sa,sa,R1,e. split. easy.
  split. easy. split. apply if_step_ct; try easy.
  eapply state_equiv_qstate_wt. apply X1. easy.
  exists sa,sa,R1,PSKIP. split. easy.
  split. easy. split. apply if_step_cf; try easy.
  eapply state_equiv_qstate_wt. apply X1. easy.
 -
  apply env_equiv_state_eq with (rmax := rmax) (s := s) in H0 as X1; try easy.
  destruct X1 as [sa [X1 X2]].
  inv X2. inv H11. inv H10.
  apply state_equiv_qstate_wt in X1 as X2; try easy.
  apply env_equiv_simple in H0 as X3; try easy.
  assert (btest_or b \/ ~ btest_or b).
  destruct b; try easy. 1-3:right; easy. left; easy. right; easy.
  destruct H6. destruct b; try easy.
  assert (simple_ses (l++l1)) as X4.
  unfold simple_tenv in X3. eapply X3. simpl. left. easy.
  inv H.
  apply simple_ses_app_r in X4 as X5.
  apply ses_len_simple in X5 as X6. destruct X6 as [n' X6].
  specialize (fch_mut_state 0 1 n'
           (fst (grab_bool bl m 1)) (snd (grab_bool bl m 1))) as X7.
  assert (freeVarsNotCPExp env e).
  unfold freeVarsNotCPExp in *. intros; simpl in *.
  eapply H2. right. apply H. easy.
  assert (simple_tenv ((l1, CH) :: nil)).
  unfold simple_tenv in *. intros. simpl in *. destruct H7; try easy. inv H7.
  easy.
  assert (env_state_eq ([(l1, CH)])
                   ([(l1,
                    Cval (fst (grab_bool bl m 1))
                      (mut_fch_state 0 1 n'
                         (snd (grab_bool bl m 1))))])).
  repeat constructor.
  assert (qstate_wt
                   ([(l1,
                    Cval (fst (grab_bool bl m 1))
                      (mut_fch_state 0 1 n'
                         (snd (grab_bool bl m 1))))])).
  unfold qstate_wt in *.
  intros. simpl in *. destruct H9; try easy. inv H9.
  apply grab_bool_gt. eapply X2. left. easy. lia.
  assert (env_equiv ([(l1, CH)]) ([(l1, CH)])). constructor.
  destruct (IHlocus_system H ([(l1, CH)]) H10 H7 ((l1,(Cval (fst (grab_bool bl m 1))
    (mut_fch_state 0 1 n' (snd (grab_bool bl m 1)))))::nil) H8 H9) 
              as [sa [sa' [ra [ea [Y1 [Y2 [Y3 Y4]]]]]]].
  apply qm_step_prob_1 with (T := [(l1, CH)]) (T' := [(l1, CH)]) in Y3 as Y5; try easy; subst.
  apply simple_env_same_state with (l := l1) in Y3 as Y5; try easy.
  inv Y5. inv H18. inv H17.
  destruct (assem_bool_exists 1 n' m m0 bl bl0) as [mv [fv Y6]].
  inv Y2. inv H18. inv H17.
  apply state_equiv_single_eq in Y1 as Y7. inv Y7.
  exists ([([(i, BNum v, BNum (S v))] ++ l1, Cval m bl)]),
      (((i,BNum v,BNum (S v))::l1, (Cval mv fv))::nil),R1,(If (BTest i v) ea).
  split. easy. split. constructor. 1-2: constructor.
  apply simple_env_same_state with (l := l1) in Y3 as Y5; try easy.
  split. apply if_sem_q with (n := n') (fc := Cval (fst (grab_bool bl m 1))
     (mut_fch_state 0 1 n' (snd (grab_bool bl m 1)))) (fc' := (Cval m0 bl0)); try easy.
  unfold qstate_wt in *. intros; simpl in *. 
  destruct H12; try easy. inv H12.
  assert (((i, BNum v, BNum (S v)) :: l1, Cval m bl)
    = ((i, BNum v, BNum (S v)) :: l1, Cval m bl) \/ False).
  left. easy. apply X2 in H12.
  apply assem_bool_gt in Y6 as X10; try easy. lia.
  apply eval_bexp_exists with (s := nil) (l1 := l1) (m := m) (f := bl) in H as X10.
  destruct X10 as [f' X10].
  assert (exists b', get_core_bexp b = Some b').
  inv X10; try easy; simpl in *.
  1-4:exists (BTest z i); easy.
  destruct H7 as [b' Y2].
  exists ([(l ++ l1, Cval m bl)]), ((l++l1,Cval m f')::nil),R1,(If b' e).
  split. easy. split. constructor. 1-2:constructor.
  split. apply if_sem_side with (n0 := n); try easy.
  unfold qstate_wt in *.
  intros. simpl in *. destruct H7; try easy. inv H7. eapply X2. left. easy.
- 
  apply env_equiv_state_eq with (rmax := rmax) (s := s) in H0 as X1; try easy.
  destruct X1 as [sa [X1 X2]].
  apply state_equiv_qstate_wt in X1 as X3; try easy.
  apply env_equiv_simple in H0 as X4; try easy.
  assert (e1 = PSKIP \/ ~ e1 = PSKIP).
  destruct e1; try easy. left; try easy.
  1-7:right; easy. destruct H1; subst.
  exists sa,sa, R1, e2.
  split. easy. split. easy.
  split. apply seq_step_2. easy.
  assert (freeVarsNotCPExp env e1).
  unfold freeVarsNotCPExp in *. intros; simpl in *.
  eapply H2. apply in_app_iff. left. apply H5.
  easy.
  assert (env_equiv T T) by constructor.
  destruct (IHlocus_system1 H5 T H6 X4 sa X2 X3) as [sa1 [s' [r [e' [Y1 [Y2 [Y3 Y4]]]]]]].
  exists sa1,s',r,(PSeq e' e2).
  split. eapply state_trans. apply X1. easy. split. easy.
  split. apply seq_step_1. easy. easy.
-
  apply env_equiv_state_eq with (rmax := rmax) (s := s) in H0 as X1; try easy.
  destruct X1 as [sa [X1 X2]].
  apply state_equiv_qstate_wt in X1 as X3; try easy.
  exists sa,sa,R1,PSKIP. split. easy. split. easy.
  split. constructor. lia. easy.
- apply env_equiv_state_eq with (rmax := rmax) (s := s) in H4 as X1; try easy.
  destruct X1 as [sa [X1 X2]].
  apply state_equiv_qstate_wt in X1 as X3; try easy.
  exists sa,sa,R1,(PSeq (If (subst_bexp b i l) (subst_pexp e i l)) (For i (Num (S l)) (Num h) b e)).
  split. easy. split. easy.
  split. apply for_step_s. easy. easy.
Qed.


Lemma type_cbexp_no_qtype: forall env b n t, type_cbexp env b t -> t <> QT n.
Proof.
  intros. induction H; try easy.
Qed.

Lemma simp_bexp_no_qtype: forall env b n l, 
        type_bexp env b (QT n,l) -> simp_bexp b = None.
Proof.
 intros. remember (QT n, l) as t. induction H; simpl in *; try easy.
 apply type_cbexp_no_qtype with (n := n) in H. inv Heqt. easy.
 apply IHtype_bexp in Heqt. rewrite Heqt. easy.
Qed.

Lemma type_sem_local_bexp: forall env b n l l1 v v' s sa, type_bexp env b (QT n, l) ->
  eval_bexp ((l ++ l1, v) :: s) b ((l ++ l1, v') :: s) ->
  eval_bexp ((l ++ l1, v) :: sa) b ((l ++ l1, v') :: sa).
Proof.
  intros. induction H; try easy.
  inv H0. constructor. easy.
  inv H0. constructor. easy.
  inv H0. constructor. easy.
  inv H0. constructor. easy.
Qed.

Lemma type_sem_local: forall e e' rmax q env T T' s1 s2 s r, simple_tenv T ->
   env_state_eq T s1 -> @locus_system rmax q env T e T' ->
      @step rmax env (s1 ++ s2) e r s e' -> 
            (exists s1', s = s1' ++ s2 /\ 
           @step rmax env s1 e r s1' e').
Proof.
  intros. generalize dependent e'. 
  generalize dependent s1. generalize dependent s2. generalize dependent s.
  induction H1; intros;simpl in *; subst; try easy.
- apply IHlocus_system in H3; try easy.
- apply env_state_eq_app in H0 as X1; try easy.
  destruct X1 as [sa [sb [X1 [X2 X3]]]]. subst.
  apply env_state_eq_same_length in X1; try easy.
  destruct X1. apply simple_tenv_app_l in H as X1.
  rewrite <- app_assoc in *.
  destruct (IHlocus_system X1 s0 (sb++s2) sa H3 e' H2) as [sc [Y1 Y2]]; simpl in *; subst.
  exists (sc++sb). rewrite app_assoc. split; try easy.
  apply step_sem_local with (s1 := sb) in Y2; try easy.
- inv H2. inv H0. exists nil. simpl. split; try easy. constructor.
- inv H4.
  exists (s1). split; try easy.
  apply let_step; try easy.
- inv H4. inv H3. simpl in *. inv H5.
  exists ((l, va') :: l2).
  split; try easy.
  apply let_step_q; try easy.
- inv H2. inv H8. inv H9. inv H3.
  exists ([(l, Nval ra ba)]); simpl in *. split. easy. constructor. easy.
- inv H2. inv H8. inv H9. inv H3.
  exists ([(l ++ l0, Cval m ba)]); simpl in *. split. easy.
  constructor; try easy.
- inv H2. inv H8. inv H9. inv H3.
  exists ([([a], Hval (fun i : nat => update allfalse 0 (r0 i)))]); simpl in *.
  split; try easy. try constructor; try easy.
- inv H2. inv H8. inv H9. inv H3.
  exists ([([a], Nval C1 (fun j : nat => bl j 0))]); simpl in *.
  split; try easy. try constructor; try easy.
- inv H2. inv H8. inv H9. inv H3.
  exists ([([a] ++ l, Cval (m0 * 2 ^ n) (eval_h_ch n m0 bl))]); simpl in *.
  split; try easy. try constructor; try easy.
- inv H3; try easy.
  exists s1. split; try easy.
  apply if_step_ct; try easy.
  exists s1. split; try easy.
  apply if_step_cf; try easy.  
  apply type_bexp_only with (t := (QT n, l)) in H0; subst; try easy.
- 
  assert (simple_tenv ((l1, CH) :: nil)).
  unfold simple_tenv in *. intros. simpl in *; try easy. destruct H4; try easy.
  inv H4.
  specialize (H (l ++ a) CH).
  assert ((l ++ a, CH) = (l ++ a, CH) \/ False).
  left. easy. apply H in H4.
  apply simple_ses_app_r in H4. easy.
  specialize (IHlocus_system H4). inv H3.
  apply simp_bexp_no_qtype in H0. rewrite H0 in *. easy.
  apply simp_bexp_no_qtype in H0. rewrite H0 in *. easy.
  inv H2. inv H13. inv H14. inv H5.
  inv H0. simpl in *. inv H8. inv H3.
  assert (env_state_eq ([(l1, CH)]) ([(l1, fc)])).
  constructor. constructor. inv H11. constructor.
  destruct (IHlocus_system ((l1, fc') :: s') s2  ([(l1, fc)]) H0 e'0 H12) as [sa [X1 X2]].
  destruct sa; try easy. 
  apply simple_env_same_state with (s := ([(l1, fc)]))
           (r := R1) (s' := nil) (e' := e'0) in H1 as X3; try easy.
  unfold simple_tenv in H4. eapply H4. simpl. left. easy.
  inv X1. simpl in *.
  exists (((i, BNum v, BNum (S v)) :: l1, fc'') :: sa).
  simpl in *. split. easy.
  apply if_sem_q with (n := n0) (fc0 := fc) (fc'0 := fc'); try easy.
  inv H2. inv H11. inv H12. inv H5. apply type_bexp_only with (t := (QT n, l)) in H10; try easy.
  inv H10. apply app_inv_head_iff in H3. subst.
  exists ([(l0 ++ l1, Cval m0 f')]).
  split; try easy.
  apply if_sem_side with (n := n0); try easy.
  apply type_sem_local_bexp with (env := env) (n := n0) (s := s2); try easy.
-
  inv H2.
  apply IHlocus_system1 in H9; try easy.
  destruct H9 as [sa [X1 X2]]. exists sa. split; try easy.
  apply seq_step_1. easy.
  exists s1. split; try easy.
  constructor.
- 
  inv H2. exists s1. split; try easy.
  constructor. easy.
  exists s1. split; try easy.
  constructor. easy.
- inv H5. lia.
  exists s1. split; try easy. constructor. easy.
Qed.

Lemma type_aexp_subst: forall env env0 a x n, type_aexp env a (CT, nil) -> 
    AEnv.Equal (AEnv.add x CT env0) env -> type_aexp env0 (subst_aexp a x n) (CT, nil).
Proof.
  intros. remember (CT,nil) as t.
  induction H. simpl in *. bdestruct (x=?b). constructor. constructor.
  apply aenv_mapsto_equal with (s2 := (AEnv.add x CT env0)) in H; try easy.
  apply AEnv.add_3 in H; try easy.
  easy.
  simpl in *. constructor. subst.
  inv H2. simpl. apply plus_type with (t1 := (CT, [])) (t2 := (CT, [])); try easy.
  apply IHtype_aexp1; easy.
  apply IHtype_aexp2; easy.
  constructor. subst.
  inv H2. simpl. apply mult_type with (t1 := (CT, [])) (t2 := (CT, [])); try easy.
  apply IHtype_aexp1; easy.
  apply IHtype_aexp2; easy.
  constructor.
Qed.

Lemma type_subst : forall e rmax q enva env T T' x n, AEnv.Equal (AEnv.add x CT env) enva ->
      @locus_system rmax q enva T e T' ->
    ~ AEnv.In (elt:=ktype) x env -> simple_tenv T -> @locus_system rmax q env T (subst_pexp e x n) T'.
Proof.
  intros. 
  generalize dependent env.
  induction H0; intros; subst; simpl in *; try easy.
  apply eq_ses with (T'0 := T'); try easy.
  apply IHlocus_system; try easy.
  apply simple_tenv_app_l in H2.
  specialize (IHlocus_system H2 env0 H H1).
  apply sub_ses. easy.
  constructor.
  bdestruct (x0 =? x). subst.
  assert (AEnv.In (elt:=ktype) x env).
  exists CT. apply aenv_mapsto_equal with (s1 := (AEnv.add x CT env0)); try easy.
  apply AEnv.add_1. easy. easy.
  apply assign_ses; try easy. apply type_aexp_subst with (env := env); try easy.
  assert (~ AEnv.In (elt:=ktype) x0 (AEnv.add x CT env0)).
  intros R. destruct R. apply aenv_mapsto_equal with (s2 := env) in H6; try easy.
  assert (AEnv.In x0 env). exists x1. easy. easy.
  intros R.
  assert (AEnv.In (elt:=ktype) x0 (AEnv.add x CT env0)).
  destruct R. exists x1. apply AEnv.add_2; try lia.
  easy. easy.
  apply IHlocus_system; try easy.
  apply AEnvFacts.Equal_trans with (m' := (AEnv.add x0 CT (AEnv.add x CT env0))); try easy.
  apply AEnvFacts.Equal_mapsto_iff.
  intros. split. intros. bdestruct (k =? x0).
  subst. apply AEnv.add_3 in H6; try lia.
  apply aenv_mapsto_add1 in H6; subst.
  apply AEnv.add_1. easy.
  bdestruct (k =? x). subst.
  apply aenv_mapsto_add1 in H6; subst.
  apply AEnv.add_2. lia. apply AEnv.add_1. easy.
  apply AEnv.add_2; try lia.
  apply AEnv.add_2; try lia.
  apply AEnv.add_3 in H6; try lia.
  apply AEnv.add_3 in H6; try lia.
  easy. intros.
  bdestruct (k =? x).
  subst. apply AEnv.add_3 in H6; try lia.
  apply aenv_mapsto_add1 in H6; subst.
  apply AEnv.add_1. easy.
  bdestruct (k =? x0). subst.
  apply aenv_mapsto_add1 in H6; subst.
  apply AEnv.add_2. lia. apply AEnv.add_1. easy.
  apply AEnv.add_2; try lia.
  apply AEnv.add_2; try lia.
  apply AEnv.add_3 in H6; try lia.
  apply AEnv.add_3 in H6; try lia.
  easy.
  apply AEnvFacts.Equal_mapsto_iff.
  intros. split; intros.
  bdestruct (k =? x0). subst.
  apply aenv_mapsto_add1 in H6; subst.
  apply AEnv.add_1. easy.
  apply AEnv.add_3 in H6.
  apply AEnv.add_2. lia.
  apply aenv_mapsto_equal with (s1 := (AEnv.add x CT env0)); try easy. lia.
  bdestruct (k =? x0). subst.
  apply aenv_mapsto_add1 in H6; subst.
  apply AEnv.add_1. easy.
  apply AEnv.add_3 in H6.
  apply AEnv.add_2. lia.
  apply aenv_mapsto_equal with (s1 := env); try easy. lia.
  intros R. destruct R.
  apply AEnv.add_3 in H6.
  assert (AEnv.In (elt:=ktype) x env0).
  exists x1. easy. easy. lia.
  bdestruct (x0 =? x). subst.
  assert (AEnv.In (elt:=ktype) x env).
  exists CT.
  apply aenv_mapsto_equal with (s1 := (AEnv.add x CT env0)); try easy.
  apply AEnv.add_1. easy. easy.
  apply meas_m1; try easy.
  apply aenv_mapsto_equal with (s2 := AEnv.add x CT env0) in H; try easy.
  apply AEnv.add_3 in H; try easy.
  bdestruct (x =? y). subst. apply aenv_mapsto_add1 in H. easy.
  easy.
  intros R.
  assert (AEnv.In (elt:=ktype) x0 env).
  destruct R.
  assert (AEnv.MapsTo x0 x1 (AEnv.add x CT env0)).
  apply AEnv.add_2; try lia.
  easy. exists x1. apply aenv_mapsto_equal with (s1 := (AEnv.add x CT env0)); try easy.
  easy.
  apply IHlocus_system; try easy.
  unfold simple_tenv in *.
  intros. simpl in *. inv H6. inv H7.
  assert (((y, BNum 0, BNum n0) :: a, CH) = ((y, BNum 0, BNum n0) :: a, CH) 
         \/ In ((y, BNum 0, BNum n0) :: a, CH) T).
  simpl. left. easy. apply H2 in H6. simpl in *. inv H6. easy.
  eapply H2. right. apply H7.
  apply AEnvFacts.Equal_mapsto_iff. intros. split. intros.
  bdestruct (k =? x0); subst.
  apply AEnv.add_3 in H6; try lia.
  apply aenv_mapsto_add1 in H6. subst. apply AEnv.add_1. easy.
  apply AEnv.add_2; try lia.
  apply aenv_mapsto_equal with (s1 := (AEnv.add x CT env0)); try easy.
  bdestruct (k =? x); subst. apply aenv_mapsto_add1 in H6.
  subst. apply AEnv.add_1. easy.
  apply AEnv.add_3 in H6; try lia. apply AEnv.add_3 in H6; try lia.
  apply AEnv.add_2; try lia. easy.
  intros.
  bdestruct (k =? x); subst.
  apply AEnv.add_3 in H6; try lia.
  apply aenv_mapsto_equal with (s2 := (AEnv.add x CT env0)) in H6; try easy.
  apply aenv_mapsto_add1 in H6. subst. apply AEnv.add_1. easy.
  apply AEnv.add_2; try lia.
  bdestruct (k =? x0); subst. apply aenv_mapsto_add1 in H6. subst. apply AEnv.add_1. easy.
  apply AEnv.add_3 in H6; try lia. apply AEnv.add_2; try lia.
  apply aenv_mapsto_equal with (s2 := (AEnv.add x CT env0)) in H6; try easy.
  apply AEnv.add_3 in H6; try lia. easy.
  intros R. destruct R. apply AEnv.add_3 in H6.
  assert (AEnv.In (elt:=ktype) x env0). exists x1. easy. easy. lia.
  apply appu_ses_nor with (n1 := n0); try easy.
Admitted.

Lemma simple_ses_locus_subst: forall l i v, simple_ses l -> subst_locus l i v = l.
Proof.
  intros. induction l. simpl in *. easy.
  simpl in *. inv H. rewrite IHl; try easy.
  unfold subst_range in *.
  unfold simple_bound in *. destruct x; try easy. destruct y; try easy.
Qed.

Lemma simple_ses_add_end_locus: forall l l1 i v, simple_ses l1 -> subst_locus (l ++ l1) i v = (subst_locus l i v) ++ l1.
Proof.
  intros. induction l. simpl in *.
  rewrite simple_ses_locus_subst; try easy.
  simpl in *. rewrite IHl. easy.
Qed.

Lemma simple_ses_add_end: forall l T i v, simple_ses l
  -> (add_end l (subst_type_map T i v)) = subst_type_map (add_end l T) i v. 
Proof.
  intros. induction T; try easy.
  simpl in *. destruct a. simpl in *.
  rewrite simple_ses_add_end_locus; try easy.
Qed.

Lemma locus_system_prolong: forall rmax env l T Ta e, @locus_system rmax QM env T e Ta
    -> is_cval_t T -> length T <= 1 -> simple_ses l -> @locus_system rmax QM env (add_end l T) e (add_end l Ta).
Proof.
  intros. remember QM as q. induction H; subst; try easy.
  apply eq_ses with (T'0 := add_end l T').
  apply IHlocus_system; try easy.
  apply locus_system_qm_single_same in H; try easy.
  apply env_equiv_add_end. easy.
  destruct T. simpl in *.
  apply locus_system_qm_single_same in H as X1; try easy.
  inv X1. simpl in *.
  replace ((add_end l T1)) with ([] ++ (add_end l T1)) by easy.
  apply sub_ses. apply IHlocus_system; try easy. lia. simpl;lia.
  simpl in *. destruct p. destruct s0;try easy.
  assert (length (T ++ T1) = 0) by lia.
  apply length_zero_iff_nil in H3.
  apply app_eq_nil in H3. destruct H3; subst; try easy. simpl in *.
  apply locus_system_qm_single_same in H as X1; try easy.
  apply env_equiv_single_prog in X1 as X2; try easy.
  destruct X2. simpl in *. destruct T'. simpl in *. inv X1. simpl in *.
  destruct p. destruct s0; try easy.
  destruct T'; try easy. simpl in *.
  apply IHlocus_system; try easy.
  simpl in *. constructor.
  apply assign_ses; try easy. apply IHlocus_system; try easy.
  unfold add_end in *.
  repeat rewrite <- app_assoc. apply appu_ses_ch with (n0 := n); try easy.
  simpl in *. apply appu_ses_h_ch with (m0 := m); try easy.
  apply qif_ses; try easy. apply IHlocus_system; try easy.
  unfold add_end in *.
  repeat rewrite <- app_assoc.
  apply qif_ses_ch with (n0 := n); try easy.
  apply IHlocus_system; try easy.
  apply locus_system_qm_single_same in H as X1.
  apply env_equiv_single_prog in X1 as X2; try easy. destruct X2.
  apply pseq_ses_type with (T3 := (add_end l T1)); try easy.
  apply IHlocus_system1; try easy.
  rewrite <- H5 in H1.
  apply IHlocus_system2; try easy.
  easy. easy.
  apply qfor_ses_no. easy.
  repeat rewrite simple_ses_add_end; try easy.
  apply qfor_ses_ch; try easy.
  intros. specialize (H5 v H6).
  rewrite simple_ses_add_end in H5; try easy.
  assert ((add_end l (subst_type_map T i (v + 1))) = ((subst_type_map (add_end l T) i ((v + 1))))).
  rewrite simple_ses_add_end; try easy.
  rewrite H7 in H5. apply H5; try easy.
  apply is_cval_t_subst with (a := l0); try easy.
  rewrite length_subst with (v := l0). easy.
Qed.

Lemma locus_system_skip_equiv: 
  forall rmax q env T T1, @locus_system rmax q env T PSKIP T1 -> env_equiv T T1.
Proof.
  intros. remember PSKIP as e. induction H; try easy.
  apply env_trans with (T2 := T'); try easy. apply IHlocus_system;easy.
  apply equiv_env_cong. apply IHlocus_system;easy. constructor.
Qed.

Lemma type_preserve: forall rmax q env T T' s s' r e e', @locus_system rmax q env T e T' 
  -> env_state_eq T s -> freeVarsNotCPExp env e -> simple_tenv T
      -> @step rmax env s e r s' e'
       -> exists Ta Tb, env_state_eq Ta s' 
            /\ env_equiv Ta Tb /\ @locus_system rmax q env Tb e' T'.
Proof.
  intros. generalize dependent e'. generalize dependent s. generalize dependent s'.
  induction H; intros;simpl in *; subst.
 -
  destruct (IHlocus_system H1 H2 s' s0 H3 e' H4) as [Ta [Tb [X1 [X2 X3]]]].
  exists Ta,Tb. split. easy. split. easy.
  apply eq_ses with (T'0 := T'); try easy.
 -
  apply env_state_eq_app in H0 as X1; try easy.
  destruct X1 as [s1 [s2 [X1 [X2 X3]]]].
  subst. apply env_state_eq_same_length in X1; try easy.
  destruct X1. apply simple_tenv_app_l in H2 as X1.
  apply type_sem_local with (q := q) (env := env) (T := T) (T' := T') in H3; try easy.
  destruct H3 as [sa [Y1 Y2]]; subst.
  apply IHlocus_system in Y2; try easy. destruct Y2 as [Ta [Tb [A2 [A3 A4]]]].
  exists (Ta++T1),(Tb++T1).
  split. 
  apply env_state_eq_app_join; try easy.
  split. apply equiv_env_cong. easy.
  apply sub_ses; try easy.
 -
  inv H3. inv H0. exists nil,nil. split; constructor. constructor.
  constructor.
 - 
  inv H5. exists T,T. split; try easy.
  unfold freeVarsNotCPExp in H1. simpl in *. split; try constructor.
  apply type_subst with (enva := (AEnv.add x CT env)); try easy.
 -
  inv H5. inv H4.
  exists ((l0, CH) :: T),((l0, CH) :: T). split.
  constructor. easy.
  inv H14. simpl in *. destruct (build_state_pars m n0 v (to_sum_c m n0 v bl) bl).
  inv H16. constructor. 
  split.  constructor.
  apply type_subst with (enva := (AEnv.add x CT env)); try easy.
  unfold simple_tenv in *.
  intros; simpl in *. inv H4. inv H5.
  assert (((y, BNum 0, BNum n0) :: a, CH) = 
   ((y, BNum 0, BNum n0) :: a, CH) \/ In ((y, BNum 0, BNum n0) :: a, CH) T).
  left. easy. apply H2 in H4.
  inv H4. easy.
  eapply H2. right. apply H5.
-
  inv H4. inv H3. inv H6.
  exists ([(l, TNor)]),([(l, TNor)]).
  split. constructor. constructor. constructor. split. constructor.
  replace ([(l, TNor)]) with ([]++[(l, TNor)]) by easy.
  apply sub_ses. constructor.
  inv H3. inv H11.
-
  inv H4. inv H3. inv H11. inv H3. inv H6.
  exists ([(l ++ l', CH)]),([(l ++ l', CH)]).
  split. constructor. 1-2:constructor. split. constructor.
  replace ([(l ++ l', CH)]) with ([]++[(l ++ l', CH)]) by easy.
  apply sub_ses. constructor.
-
  inv H4. inv H3. inv H6.
  exists ([([a0], THad)]),([([a0], THad)]).
  split. constructor. 1-2:constructor. split. constructor.
  replace ([([a0], THad)]) with ([]++([([a0], THad)])) by easy.
  apply sub_ses. constructor.
  inv H3. inv H12. inv H3. inv H14.
-
  inv H4. inv H3. inv H12. inv H3. inv H12. inv H6.
  exists ([([a0], TNor)]),([([a0], TNor)]).
  split. constructor. 1-2:constructor. split. constructor.
  replace ([([a0], TNor)]) with ([]++([([a0], TNor)])) by easy.
  apply sub_ses. constructor.
  inv H3. inv H14.
-
  inv H4. inv H3. inv H13. inv H3. inv H13. inv H3. inv H7. inv H14.
  exists ([([a0]++ l0, CH)]),([([a0]++ l0, CH)]).
  split. constructor. 1-2:constructor. split. constructor.
  replace ([(a0 :: l0, CH)]) with ([]++([([a0] ++ l0, CH)])) by easy.
  replace ([([a0] ++ l0, CH)]) with ([]++([([a0] ++ l0, CH)])) by easy.
  apply sub_ses. constructor.
-
  inv H4. exists T,T. split; try easy. split. constructor. easy.
  exists T,T. split; try easy. split. constructor.
  replace T with ([] ++ T) by easy.
  apply sub_ses. constructor.
  inv H. apply type_bexp_only with (t := (CT, [])) in H10; try easy.
-
  inv H4. apply simp_bexp_no_qtype in H. rewrite H in *. easy.
  apply simp_bexp_no_qtype in H. rewrite H in *; easy.
  inv H. simpl in *. inv H7.
  inv H3. inv H5.
  assert (simple_tenv ([(l0, CH)])).
  unfold simple_tenv in *. intros. inv H; try easy. inv H3.
  assert (In ((i, BNum v, BNum (S v)) :: a, CH) ([((i, BNum v, BNum (S v)) :: a, CH)])).
  simpl. left. easy. apply H2 in H. inv H. easy.
  apply simple_env_same_state with (l := l0) in H12 as X1; try easy.
  assert (freeVarsNotCPExp env e).
  unfold freeVarsNotCPExp in *. intros. eapply H1. simpl. right. apply H3. easy.
  inv X1. inv H6.
  apply IHlocus_system in H12 as X2; try easy.
  destruct X2 as [Ta [Tb [X2 [X3 X4]]]]. inv X2. inv H7.
  apply type_state_elem_same_unique with (t := t) in H17; try easy; subst.
  apply env_equiv_single_prog in X3 as G1; try easy. destruct G1 as [G1 G2].
  assert (exists l1, Tb = ([(l1,CH)])).
  destruct Tb; try easy. destruct Tb ; try lia. unfold is_cval_t in *. destruct p; try easy.
  destruct s; try easy. exists l. easy. simpl in *. lia.
  destruct H4 as [l1 G3]; subst.
  exists ([((i, BNum v, BNum (S v)) :: l0, CH)]), ([((i, BNum v, BNum (S v)) :: l1, CH)]).
  split. constructor. constructor. inv H13. inv H16. 1-3: constructor.
  split. apply env_equiv_add_a with (a := (i, BNum v, BNum (S v))) in X3. easy.
  apply eq_ses with (T' := [((i, BNum v, BNum (S v)) :: l1, CH)]).
  replace ((i, BNum v, BNum (S v)) :: l1) with ([(i, BNum v, BNum (S v))]++l1) by easy.
  apply qif_ses_ch with (n := 1); try easy.
  apply btest_type with (n := n1); try easy.
  apply eq_ses with (T' := [(l0, CH)]); try easy.
  apply env_sym in X3.
  apply env_equiv_add_a with (a := (i, BNum v, BNum (S v))) in X3. easy.
  inv H17. inv H9. constructor. 1-2: constructor.
  unfold simple_tenv in *. eapply H. simpl in *. left. easy.
  inv H9. constructor. 1-2:constructor.
  inv H3. inv H6.
  apply type_bexp_only with (t := (QT n0, l0)) in H; try easy.
  inv H. apply app_inv_head_iff in H9. subst.
  assert (exists z v, get_core_bexp b = Some (BTest z v)).
  unfold get_core_bexp in *. destruct b; try easy. exists i, a. easy.
  exists i,a. easy.
  destruct H as [z [v' H]]. rewrite H7 in H. inv H.
  assert (exists a u v, l = ((a,BNum 0,BNum u)::[(z,BNum v,BNum (S v))]) /\ n = u + 1 /\ v' = Num v).
  inv H10; simpl in *; try easy. inv H7.
  exists a,m0,v. easy.
  inv H7. exists a,m0,v. easy. inv H7.
  exists a,m0,v. easy.
  inv H7. exists a,m0,v. easy.
  destruct H as [a [u [v [Y1 [Y2 Y3]]]]]; subst.
  exists ([((a, BNum 0, BNum u):: [(z, BNum v, BNum (S v))] ++ l2, CH)]),
        ([([(z, BNum v, BNum (S v))] ++ l2 ++ [(a, BNum 0, BNum u)], CH)]).
  split. simpl in *. constructor. 1-2: constructor.
  split.
  assert (env_equiv ([((a, BNum 0, BNum u) :: [(z, BNum v, BNum (S v))] ++ l2, CH)])
       ([((z, BNum v, BNum (S v)) :: [(a, BNum 0, BNum u)] ++ l2, CH)])). 
  replace ([((a, BNum 0, BNum u) :: [(z, BNum v, BNum (S v))] ++ l2, CH)])
   with ([([]++ (a, BNum 0, BNum u) :: (z, BNum v, BNum (S v)) :: l2, CH)]) by easy.
  replace ([((z, BNum v, BNum (S v)) :: [(a, BNum 0, BNum u)] ++ l2, CH)])
   with ([([]++ (z, BNum v, BNum (S v)) :: (a, BNum 0, BNum u) :: l2, CH)]) by easy.
  apply env_mut. 
  apply env_trans with (T2 := ([((z, BNum v, BNum (S v)) :: [(a, BNum 0, BNum u)] ++ l2, CH)])); try easy.
  simpl.
  assert (env_equiv ([((a, BNum 0, BNum u) :: l2, CH)]) ([(l2 ++ [(a, BNum 0, BNum u)], CH)])).
  apply env_equiv_end.
  apply env_equiv_add_a with (a := (z, BNum v, BNum (S v))) in H3. easy.
  apply eq_ses with (T' := [([(z, BNum v, BNum (S v))] ++ l2 ++ [(a, BNum 0, BNum u)], CH)]).
  apply qif_ses_ch with (n := 1).
  inv H10; try easy.
  apply btest_type with (n := n); try easy.
  apply btest_type with (n := n); try easy.
  apply btest_type with (n := n); try easy.
  apply btest_type with (n := n); try easy.
  apply locus_system_prolong with (l := ([(a, BNum 0, BNum u)])) in H0; try easy.
  constructor; try easy. constructor.
  apply env_sym.
  apply env_equiv_end.
- inv H4. apply IHlocus_system1 in H12; try easy.
  destruct H12 as [Ta [Tb [X1 [X2 X3]]]].
  exists Ta,Tb. split; try easy. split; try easy.
  apply pseq_ses_type with (T3 := T1); try easy.
  unfold freeVarsNotCPExp in *. intros. simpl in *.
  eapply H1. simpl. apply in_or_app. left. apply H4. easy.
  apply locus_system_skip_equiv in H as X1.
  apply env_equiv_simple in X1 as X3; try easy.
  apply env_equiv_state_eq with (rmax := rmax) (s := s') in X1 as X4; try easy.
  destruct X4 as [sa [X4 X5]].
  exists T,T1. split; try easy.
- inv H3. exists T,T. split; try easy. split. constructor.
  replace T with (nil++T). apply sub_ses. constructor. easy.
  lia.
-
  inv H6. lia.
  assert (exists m , h = l + m). exists (h -l). lia.
  destruct H6 as [m H6]; subst. assert (0 < m) by lia. clear H. clear H17.
  exists ((subst_type_map T i l)),((subst_type_map T i l)).
  split; try easy. split. constructor.
  assert (l <= l < l + m) by lia.
  apply H3 in H.
  apply pseq_ses_type with (T1 := (subst_type_map T i (l + 1))); try easy.
  replace (l+1) with (S l) by lia.
  destruct m; try easy. destruct m; try easy.
  replace (l+1) with (S l) by lia. apply qfor_ses_no; try easy.
  apply qfor_ses_ch; try easy. lia.
  intros. bdestruct (v =? l); subst. easy.
  apply H3. lia.
Qed.
