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
Inductive glocus_type : type_kmap -> glocus -> se_type ->  Prop :=
| glocus_nor : forall t l gl, In l t -> l = (gl, TNor) -> glocus_type t gl TNor
| glocus_had : forall t l gl, In l t -> l = (gl, THad) -> glocus_type t gl THad
| glocus_ch :  forall t l gl, In l t -> l = (gl, CH) -> glocus_type t gl CH.

Inductive glocus_state : gqstate -> glocus -> state_elem -> Prop :=
| gl_state : forall qs l gl s, In l qs -> l = (gl, s) -> glocus_state qs gl s. 

Inductive well_form : aenv -> type_kmap -> gqstate -> Prop :=
| well_form_nor : forall aenv t qs p r s gl, glocus_type t gl TNor -> glocus_state qs gl s -> s = (Nval p r) -> well_form aenv t qs    
| well_form_had : forall aenv t qs b gl s, glocus_type t gl THad -> glocus_state qs gl s -> s = (Hval b) -> well_form aenv t qs
| well_form_en : forall aenv t qs m b gl s, glocus_type t gl CH -> glocus_state qs gl s -> s = (Cval m b) -> well_form aenv t qs.

(*Lemma type_progress : forall rmax tenv gs s r l , well_dom tenv gs -> well_state tenv gs s -> (exists a s' p', step rmax tenv s p r l s'p') *)
