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
Require Import DisQSyntax.
Require Import DisQDef.
Require Import DisQKind.
Require Import DisQSem.
Require Import DisQType.
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

Definition range_no_overlap a b c d : Prop := ((a < b) /\ (c <= b)) \/ ((a >= d) /\ (c > d)).
Inductive well_dom_l : aenv -> type_map -> locus -> Prop :=
| well_dom_empty : forall aenv t, well_dom_l aenv t nil
| well_dom_many : forall aenv t l r1 r2 x y i i' j j' n, In l (map fst t) -> In r1 l /\ In r2 l ->
                 r1 = (x, BNum i, BNum j) -> r2 = (y, BNum i', BNum j') ->
                 range_no_overlap i j i' j'-> i >= 0 /\ j < n -> i' >= 0 /\ j' < n
                 -> well_dom_l aenv t l
| well_dom_in_range : forall aenv t l lc x r i j n, In l (map fst t) -> In r l ->
                      r = (x, BNum i, BNum j) -> AEnv.MapsTo x (QT lc n) aenv ->
                      i >= 0 /\ j < n -> well_dom_l aenv t l. 
                                                      
Inductive well_dom_g : aenv -> type_map -> glocus -> Prop :=
| well_dom_gempty : forall aenv t, well_dom_g aenv t nil
| well_dom_gmany : forall aenv t gl l1 l2 x y l1' l2', In l1 gl /\ In l2 gl ->
                   l1 = (l1', x) -> l2 = (l2', y) -> x <> y ->
                   @well_dom_l aenv t (map fst gl) ->
                   well_dom_g aenv t gl.                  

(*
Fixpoint flatten {A : Type} (l : list (list A)) : list A :=
  match l with
  | [] => []
  | x :: xs => x ++ flatten xs
  end.

Definition type_gmap2glocus (l: type_gmap):(glocus) :=
  flatten (map (fun x => match x with (l,s,v) =>
                                        (map (fun y => (y,v)) l) end) l).
 *)

Inductive glocus_type : type_gmap -> glocus -> se_type ->  Prop :=
| gl_type : forall t l l' gl s v, l = map fst gl -> In l' t -> l' = (l,s,v) -> glocus_type t gl s.
Inductive glocus_state : gqstate -> glocus -> state_elem -> Prop :=
| gl_state : forall qs l gl s, In l qs -> l = (gl, s) -> glocus_state qs gl s. 

Inductive well_formed : aenv -> type_gmap -> gqstate -> Prop :=
| well_form_nor : forall aenv t qs p r s gl, glocus_type t gl TNor -> glocus_state qs gl s -> s = (Nval p r) -> well_formed aenv t qs    
| well_form_had : forall aenv t qs b gl s, glocus_type t gl THad -> glocus_state qs gl s -> s = (Hval b) -> well_formed aenv t qs
| well_form_en : forall aenv t qs m b gl s, glocus_type t gl CH -> glocus_state qs gl s -> s = (Cval m b) -> well_formed aenv t qs.


(*Add wellformedness. well_form aenv T S is one. *)
Theorem type_progress : forall rmax aenv T T' C S, well_formed aenv T S ->
       @c_locus_system rmax aenv T C T' -> (exists la lb S' C', @m_step rmax aenv S C la lb S' C').
Proof.
  intros. generalize dependent S. intros. induction H0.
  destruct IHc_locus_system as [la [lb [S' [C' Hm_step]]]]. admit.
  exists la, lb, S', C'. destruct m.
  
Admitted.



