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

Inductive glocus_type : type_gmap -> glocus -> se_type ->  Prop :=
| glocus_nor : forall t l gl, In l t -> l = (gl, TNor) -> glocus_type t gl TNor
| glocus_had : forall t l gl, In l t -> l = (gl, THad) -> glocus_type t gl THad
| glocus_ch :  forall t l gl, In l t -> l = (gl, CH) -> glocus_type t gl CH.

Inductive glocus_state : gqstate -> glocus -> state_elem -> Prop :=
| gl_state : forall qs l gl s, In l qs -> l = (gl, s) -> glocus_state qs gl s. 

Inductive well_form : aenv -> type_gmap -> gqstate -> Prop :=
| well_form_nor : forall aenv t qs p r s gl, glocus_type t gl TNor -> glocus_state qs gl s -> s = (Nval p r) -> well_form aenv t qs    
| well_form_had : forall aenv t qs b gl s, glocus_type t gl THad -> glocus_state qs gl s -> s = (Hval b) -> well_form aenv t qs
| well_form_en : forall aenv t qs m b gl s, glocus_type t gl CH -> glocus_state qs gl s -> s = (Cval m b) -> well_form aenv t qs.

Definition insert_l (tv: qstate) (l: var) := map (fun x => match x with (a,b) =>
                                                                          ((map (fun y => (y,l)) a),b) end) tv.

Inductive cfg_eq : config -> config -> Prop :=
| cfg_nil_eq : forall c, cfg_eq c c
| cfg_commu_eq : forall m1 m2 c, cfg_eq (m1::m2::c) (m2::m1::c).

Lemma sub_wellFormConf : forall m l ms, wellFormedConf ((m,l)::ms) -> wellFormedConf ms.
Proof.
  intros. unfold wellFormedConf in *.
  intros. apply H with b.
  right. auto.
Qed.

Axiom sub_wellFormChans : forall m l ms, wellFormedChans ((m,l)::ms) -> wellFormedChans ms.
Axiom clear_lp : forall lp, (PNil::lp) = lp.

(*Add wellformedness. well_form aenv T S is one. *)
Theorem type_progress' : forall rmax aenv T T' C S, wellFormedConf C -> wellFormedChans C ->
       @c_locus_system rmax aenv T C T' -> C = nil \/ (exists la lb S' C', @m_step rmax aenv S C la lb S' C').
Proof.
  intros. generalize dependent S. induction H1.
  intros. left. easy.
  intros. right.
  assert (H' : wellFormedConf ms).
  { apply sub_wellFormConf with m l. auto.}
  assert (H0' : wellFormedChans ms).
  { apply sub_wellFormChans with m l. auto.}
  specialize (IHc_locus_system H' H0' S).
  destruct IHc_locus_system as [Hm_nil | Hms_step].
  rewrite -> Hm_nil.
  induction m. induction lp.
  exists (1%R, None),[l],S,[]. apply end_step. simpl. easy.
  induction a. rewrite clear_lp in *. auto. 
  
 (*
  induction H5
  destruct (IHm_locus_system H H0 H3 H4 H6 IHc_locus_system) as [la [lb [S' [C' IHm_step]]]].
 *) 
  
  .
  (* maybe doing this. induction H5.*)


(* below is wrong.
 intros. indEuction H0.
  exists (1%R, None), [], S, []. apply nil_step.
  destruct IHc_locus_system as [la [lb [S' [C' Hm_step]]]]. admit.
  exists la, lb, S', C'. destruct m.
*)
Admitted.



