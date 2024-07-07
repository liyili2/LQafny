Require Import Reals.
Require Import Psatz.
Require Import Complex.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat Permutation. 
Require Import Dirac.
Require
  Import QPE.
Require Import BasicUtility.
Require Import OQASM.
Require Import OQASMProof.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import DisQSyntax.
Require Import DisQDef.
Require Import DisQKind.
(**********************)
(** Unitary Programs **)
(**********************)


Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Declare Scope cexp_scope.
Delimit Scope cexp_scope with cexp.
Local Open Scope cexp_scope.
Local Open Scope nat_scope.


(* This is the semantics for basic gate set of the language. *)

Fixpoint compile_range_state (n st i:nat) (x:var) (b: rz_val) (f:posi -> val) :=
    match n with 0 => f
            | S m => (compile_range_state m st i x b f)[(x,st+m) |-> (nval (b (i+m)) allfalse)]
    end.

Fixpoint compile_ses_state' (i:nat) (l:locus) (b:rz_val) :=
   match l with nil => (fun _ => nval false allfalse)
           | ((x,BNum l,BNum r)::xl) => compile_range_state (r-l) l i x b (compile_ses_state' (i+(r-l)) xl b)
           | (_::xl) => compile_ses_state' i xl b
   end.
Definition compile_ses_state (l:locus) (b:rz_val) := compile_ses_state' 0 l b.

Fixpoint turn_oqasm_range (rmax n st i:nat) (x:var) (f:posi -> val) (r:rz_val) (b: rz_val) : option (rz_val * rz_val) :=
    match n with 0 => Some (r,b)
            | S m => match (turn_oqasm_range rmax m st i x f r b)
         with None => None
         | Some (r',b') => match f (x,st+m) with nval ba ra => Some (n_rotate rmax ra r', update b' (i+m) ba)
                                             | _ => None
                            end
               end
    end.

Fixpoint turn_oqasm_ses' (rmax i:nat) (l:locus) (f:posi -> val) (b:rz_val) :=
   match l with nil => Some (allfalse, b)
           | ((x,BNum l,BNum r)::xl) => 
               match turn_oqasm_ses' rmax (i+(r-l)) xl f b with None => None
               | Some (ra,ba) => turn_oqasm_range rmax (r-l) l i x f ra ba
               end
           | _ => None
   end.
Definition turn_oqasm_ses rmax (l:locus) (f:posi -> val) b  := turn_oqasm_ses' rmax 0 l f b.

Definition cover_n (f:rz_val) (n:nat) := fun i => if i <? n then false else f i.

Inductive match_value : nat -> state_elem -> state_elem -> Prop :=
   match_nval : forall n p r1 r2, (forall i, i < n -> r1 i = r2 i) -> match_value n (Nval p r1) (Nval p r2)
 | match_hval: forall n r1 r2, (forall i, i < n -> r1 i = r2 i) -> match_value n (Hval r1) (Hval r2)
 | match_cval: forall n m r1 r2, (forall j, j < m -> fst (r1 j) = fst (r2 j) /\
               (forall i, i < n -> (snd (r1 j)) i = (snd (r2 j)) i)) -> match_value n (Cval m r1) (Cval m r2).


Definition match_values (S1 S2: qstate) :=
  Forall2 (fun s1 s2 =>
           (match (s1,s2) with ((l,s,lc), (l',s',lc')) =>
             l = l' /\
            (match ses_len l with Some n => match_value n s s'
                                | None => False
            end) end)) S1 S2.

Definition eval_nor (rmax:nat) (env:aenv) (l:locus) (r:C) (b:rz_val) (e:exp) :=
   match compile_ses_qenv env l with (f,ss) =>
       match compile_exp_to_oqasm e with
                None => None
              | Some e' => 
       match ses_len l with None => None
            | Some na => 
           match turn_oqasm_ses rmax l (exp_sem f e' (compile_ses_state l b)) (cover_n b na)
                with None => None
                  | Some (ra,ba) => Some ((r* (Cexp (2*PI * (turn_angle ra rmax))))%C, ba)
           end
            end
       end
     end.

Fixpoint eval_ch (rmax:nat) (env:aenv) (l:locus) (m:nat) f (e:exp) :=
   match m with 0 => Some (fun _ => (C0 , allfalse))
          | S n => match eval_nor rmax env l (fst (f n)) (snd (f n)) e with None => None
              | Some (ra,ba) => match eval_ch rmax env l n f e with None => None
                 | Some fa => Some (update fa n (ra , ba))
            end
          end
   end.

Definition eval_to_had (n:nat) (b:rz_val) := (fun i => if i <? n then (update allfalse 0 (b i)) else allfalse).

Definition eval_to_nor (n:nat) (b:nat -> rz_val) := (fun i => if i <? n then b i 0 else false).

Definition all_nor_mode (f:posi -> val) := forall x n, right_mode_val OQASM.Nor (f (x,n)).

(* functions for defining boolean. *)

Fixpoint eval_eq_bool (f:nat -> C * rz_val) (m size v:nat) :=
  match m with 0 => f
           | S m' => update (eval_eq_bool f m' size v) m' 
                   (fst (f m'),update (snd (f m')) size (xorb ((a_nat2fb (snd (f m')) size) =? v) ((snd (f m')) size)))
  end.

Fixpoint eval_lt_bool (f:nat -> C * rz_val) (m size v:nat) :=
  match m with 0 => f
           | S m' => update (eval_lt_bool f m' size v) m' 
                   (fst (f m'),update (snd (f m')) size (xorb ((a_nat2fb (snd (f m')) size) <? v) ((snd (f m')) size)))
  end.

Fixpoint eval_rlt_bool (f:nat -> C * rz_val) (m size v:nat) :=
  match m with 0 => f
           | S m' => update (eval_rlt_bool f m' size v) m' 
                   (fst (f m'),update (snd (f m')) size (xorb (v <? (a_nat2fb (snd (f m')) size)) ((snd (f m')) size)))
  end.

Fixpoint grab_bool_elem (f:nat -> C * rz_val) (m size:nat) :=
  match m with 0 => (0,(fun _ => (C0,allfalse)))
           | S m' => if (snd (f m')) size then 
                  match grab_bool_elem f m' size with (i,acc) => (i+1,update acc i (f m')) end
                else grab_bool_elem f m' size
   end.
Definition grab_bool f m size := grab_bool_elem f m (size - 1).

Axiom grab_bool_gt : forall f m size, m > 0 -> size > 0 -> fst (grab_bool f m size) > 0.


Definition get_core_bexp (b:bexp) := match b with (BEq x y z a)
            => Some (BTest z a) | BLt x y z a => Some (BTest z a)  | _ => None end.

Inductive eval_bexp : qstate -> bexp -> qstate -> Prop :=
    | beq_sem_1 : forall s x a y z i l n m f lc, simp_aexp a = Some y ->
                     eval_bexp (((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l,Cval m f,lc)::s)
                         (BEq (BA x) (a) z (Num i)) 
                            (((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l,Cval m (eval_eq_bool f m n y),lc)::s)
    | beq_sem_2 : forall s x a y z i l n m f lc,
               simp_aexp a = Some y ->
                eval_bexp (((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l,Cval m f,lc)::s)
                         (BEq (a) (BA x) z (Num i))
                            (((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l,Cval m (eval_eq_bool f m n y),lc)::s)
    | blt_sem_1 : forall s x a y z i l n m f lc, 
               simp_aexp a = Some y ->
                eval_bexp ((((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l),Cval m f,lc)::s)
                       (BLt (BA x) (a) z (Num i)) 
                         ((((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l),(Cval m (eval_lt_bool f m n y)),lc)::s)

    | blt_sem_2 : forall s x a y z i l n m f lc, 
               simp_aexp a = Some y ->
                 eval_bexp ((((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l),Cval m f,lc)::s)
                        (BLt (a) (BA x) z (Num i))
                       ((((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l),(Cval m (eval_rlt_bool f m n y)),lc)::s).

Inductive find_basis_elems (n n':nat) (f:rz_val) (fc:nat -> C*rz_val): 
            nat -> nat -> (nat -> C * rz_val) -> Prop :=
  find_basis_empty: find_basis_elems n n' f fc 0 0 (fun _ => (C0,allfalse))
 | find_basis_many_1: forall i m acc, find_basis_elems n n' f fc i m acc -> 
            f = cut_n (lshift_fun (snd (fc i)) n') n 
         -> find_basis_elems n n' f fc (S i) (S m) (update acc m (fc i))
 | find_basis_many_2: forall i m acc, find_basis_elems n n' f fc i m acc -> 
            f <> cut_n (lshift_fun (snd (fc i)) n') n -> find_basis_elems n n' f fc (S i) m acc.

(* The proof has been given in VQO based on the fact of quantum states. *)
Axiom find_basis_elems_same: forall m1 n n1 f r r' mv fv,
      (forall j : nat,
      j < m1 ->
      fst (r j) = fst (r' j) /\
      (forall i : nat, i < n1 -> snd (r j) i = snd (r' j) i)) ->
      find_basis_elems n n1 f r m1 mv fv ->
      (exists fv', find_basis_elems n n1 f r' m1 mv fv' /\ match_value n1 (Cval mv fv) (Cval mv fv')).

Inductive assem_elem : nat -> nat -> rz_val -> (nat-> C * rz_val) -> list nat -> Prop :=
    assem_elem_0 : forall size c f, assem_elem 0 size c f nil
  | assem_elem_st : forall size c f m l, assem_elem m size c f l -> cut_n (snd (f m)) size = c
                 -> assem_elem (S m) size c f (m::l)
  | assem_elem_sf : forall size c f m l, assem_elem m size c f l -> cut_n (snd (f m)) size <> c
                 -> assem_elem (S m) size c f l.

Definition combine_two (n:nat) (f:rz_val) (g:rz_val) :=
    (fun x => if x <? n then f x else g (x-n)).

Fixpoint assem_list (m base n:nat) (f:rz_val) (fc: nat -> C * rz_val) (acc:nat -> C*rz_val) :=
    match m with 0 => (base, acc)
               | S m' => match assem_list m' base n f fc acc with (mv, fv) => 
                           (S mv, (update fv mv (fst (fc m'), combine_two n f (snd (fc m')))))
                        end
    end.

(* first n is length of l and second is length of l1. third is num of elements *)
Inductive assem_bool (n n':nat): nat -> (nat-> C * rz_val) -> state_elem -> state_elem -> Prop :=
    assem_bool_empty: forall f fc, assem_bool n n' 0 f fc (Cval 0 (fun _ => (C0,allfalse)))
  | assem_bool_many_1: forall i m m' f fc acc fv, assem_bool n n' i f (Cval m fc) (Cval m' acc) ->
        find_basis_elems n n' (cut_n (snd (f i)) n) fc m 0 fv ->
               assem_bool n n' (S i) f (Cval m fc) (Cval (S m') (update acc m' (f i)))
  | assem_bool_many_2: forall i m m' f fc acc mv fv ma fa, assem_bool n n' i f (Cval m fc) (Cval m' acc) ->
        0 < mv -> find_basis_elems n n' (cut_n (snd (f i)) n) fc m mv fv ->
        assem_list mv m' n (cut_n (snd (f i)) n) fv acc = (ma, fa) -> 
               assem_bool n n' (S i) f (Cval m fc) (Cval ma fa).

Fixpoint subst_qstate (l:qstate) (x:var) (n:nat) :=
  match l with nil => nil
          | (y,v,lc)::yl => (subst_locus y x n,v,lc)::(subst_qstate yl x n)
  end.
Definition subst_state (l:state) (x:var) n := (fst l,subst_qstate (snd l) x n).

Fixpoint loc_memb (m: memb) :=
  match m with Memb l lp => l
          | LockMemb l p lp => l
          | NewVMemb x n m' => loc_memb m'
          | NewCMemb x n m' => loc_memb m'
  end.

Definition alltrue := fun (_:nat) => true.
(* single process semantics. *)
Inductive p_step {rmax:nat}
  : aenv -> qstate -> process -> R -> qstate -> process -> Prop :=
  | self_pstep : forall aenv s Q, p_step aenv s Q (1:R) s Q  
  | if_pstep_t : forall aenv s b P Q, simp_cbexp b = Some true -> p_step aenv s (PIf b P Q) (1:R) s P
  | if_pstep_f : forall aenv s b P Q, simp_cbexp b = Some false -> p_step aenv s (PIf b P Q) (1:R) s Q
  | op_pstep   : forall aenv s a l m b e ba Q lc, eval_ch rmax aenv a m b e = Some ba ->
                   p_step aenv ((a++l, Cval m b,lc)::s) (AP (CAppU a e) Q) (1:R) ((a++l, Cval m ba,lc)::s) Q
  | mea_pstep   : forall aenv s l x a n v r va va' lc Q k, AEnv.MapsTo a (QT lc n) aenv -> @pick_mea n va (r,v) ->
                                                   k = [(a, BNum 0, BNum n)] -> build_state_ch n v va = Some va' ->
                 p_step aenv (((a,BNum 0, BNum n)::l, va, lc)::s) (AP (CMeas x k) Q) r ((l, va', lc)::s) (subst_pexp Q x v).

(* single memb semantics *)
Inductive m_step {rmax:nat}
  : aenv -> qstate -> memb -> R -> var -> qstate -> memb -> Prop :=
  | end_step : forall aenv s l,  m_step aenv s (Memb l []) (1:R) l s (Memb l [])
  | rev_step : forall aenv s m l P lp, m = (LockMemb l P lp) -> m_step aenv s m (1:R) l s (Memb l (P::lp)) 
  | move_step : forall aenv s m l lp P s' P' r, m = (LockMemb l P lp) -> @p_step rmax aenv s P r s' P' -> m_step aenv s m r l s' (Memb l lp) (*TODO: rewrite MOVE*)
  | newvar_step : forall aenv s m n x v l lc,  lc = loc_memb m ->
                  m_step aenv ((l, v, lc)::s) (NewVMemb x n m) (1:R) lc ((l++[(x, BNum 0, BNum n)], Cval n (fun _ => (C0,allfalse)), lc)::s) m.

(* multi-memb semantics *)
Definition inv_sqrt2 : R := / sqrt 2.
Definition cinv_sqrt2: C := inv_sqrt2%C.

Inductive cf_step {rmax:nat}
  : aenv -> qstate -> config -> R -> list var -> qstate -> config -> Prop :=
  | send_rev_sem : forall aenv s x y l1 l2 n m1 m2 cf a P Q,
                   simp_aexp a = Some n -> cf_step aenv s ((LockMemb l1 (AP (Send x a) P) m1)::(LockMemb l2 (AP (Recv x y) Q) m2)::cf) (1:R) (l1::[l2]) s ((Memb l1 (P::m1))::(Memb l2 (Q::m2))::cf)
  | newchan_step : forall aenv l l' v v' lc1 lc2 c n m1 m2 cf s,
                   loc_memb m1 = lc1 /\ loc_memb m2 = lc2 ->
                   cf_step aenv ((l,v,lc1)::(l',v',lc2)::s) ((NewCMemb c n m1)::(NewCMemb c n m2)::cf) (1:R) (lc1::[lc2]) ((l++[(c,BNum 0, BNum n)], Cval n (fun i => if i =? 0 then (cinv_sqrt2,allfalse) else (cinv_sqrt2,alltrue)), lc1)::(l'++[(c,BNum 0,BNum n)], Cval n (fun i => if i =? 0 then (cinv_sqrt2,allfalse) else (cinv_sqrt2,alltrue)), lc2)::s) (m1::m2::cf) .

Inductive steps {rmax:nat}
           : nat -> aenv -> qstate -> config -> R -> qstate -> Prop :=
   steps_0 : forall env s, steps 0 env s [] (1:R) s
 | steps_n : forall n env s e r s' e' l, @cf_step rmax env s e r l s' e'
                 -> steps n env s' e' r s -> steps (S n) env s e r s.

