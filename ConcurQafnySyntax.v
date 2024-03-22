Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import Classical_Prop.
Require Import MathSpec.
(*Require Import OQASM.*)
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


Inductive ktype := CT | QT (n:nat).

Definition meet_ktype (a1 a2: ktype) := 
       match a1 with CT => (match a2 with CT => CT | _ => a2 end)
                | QT n => match a2 with QT m => QT (n+m) | _ => QT n end end.

Inductive bound := BVar (v:var) (n:nat) | BNum (n:nat).

Definition simple_bound (b:bound) :=
   match b with BNum n => True | BVar x n => False end.

Definition range : Set := var * bound * bound.

Definition locus : Type := list range.

Inductive aexp := BA (x:var) | Num (n:nat)
         | APlus (e1:aexp) (e2:aexp) | AMult (e1:aexp) (e2:aexp).

Coercion BA : var >-> aexp.

Coercion Num: nat >-> aexp.


Notation "e0 [+] e1" := (APlus e0 e1) (at level 50) : cexp_scope.
Notation "e0 [*] e1" := (AMult e0 e1) (at level 50) : cexp_scope.

Inductive varia := AExp (x:aexp) | Index (x:var) (v:aexp).

Coercion AExp : aexp >-> varia.

Notation "e0 [ e1 ]" := (Index e0 e1) (at level 50) : cexp_scope.

Inductive singleGate := H_gate | X_gate | RZ_gate (f:nat) (*representing 1/2^n of RZ rotation. *).

Inductive cbexp := CEq (x:aexp) (y:aexp) | CLt (x:aexp) (y:aexp).

Inductive bexp :=  CB (c:cbexp)
                  | BEq (x:varia) (y:varia) (i:var) (a:aexp)
                    (* x = n @ z[i] --> conpare x and n --> put result in z[i] *)
                  | BLt (x:varia) (y:varia) (i:var) (a:aexp) 
                    (* x < n @ z[i] --> conpare x and n --> put result in z[i] *)
                  | BTest (i:var) (a:aexp) (* z[i] = 0 or 1 *)
                  | BNeg (b:bexp).

Notation "e0 [=] e1 @ e3 [ e4 ]" := (BEq e0 e1 e3 e4) (at level 50) : cexp_scope.

Notation "e0 [<] e1 @ e3 [ e4 ]" := (BLt e0 e1 e3 e4) (at level 50) : cexp_scope.

Notation "* e0 [ e1 ]" := (BTest e0 e1) (at level 50) : cexp_scope.

Inductive maexp := AE (n:aexp) | Meas (x:var).

Coercion AE : aexp >-> maexp.

(*compile to OQASM directly.  exp -> OQASM -> SQIR *)
Inductive exp := SKIP (x:var) (a:aexp) | X (x:var) (a:aexp)
        | CU (x:var) (a:aexp) (e:exp)
        | RZ (q:nat) (x:var) (a:aexp)  (* 2 * PI * i / 2^q *)
        | RRZ (q:nat) (x:var) (a:aexp)  
        | SR (q:nat) (x:var) (* a series of RZ gates for QFT mode from q down to b. *)
        | SRR (q:nat) (x:var) (* a series of RRZ gates for QFT mode from q down to b. *)
        (*| HCNOT (p1:posi) (p2:posi) *)
        | QFT (x:var) (b:nat) (* H on x ; CR gates on everything within (size - b). *)
        | RQFT (x:var) (b:nat)
       (* | H (p:posi) *)
        | Seq (s1:exp) (s2:exp).

Inductive type := Phi (b:nat) | Nor.

Inductive single_u := RH (p:varia) | SQFT (x:var) | SRQFT (x:var).

Inductive cexp := CSKIP
             | CLet (x: var) (n: maexp) (e:cexp) 
             | CAppU (l: locus) (e: exp)
             | CSeq (s1: cexp) (s2: cexp)
             | Send (c: nat) (a: aexp)
             | Recv (c: nat) (x: var)
             | CMeas (x: var) (n: maexp) (* looks like let expression? *)
             | NewC (x: var) (n: nat).

Inductive process := PNil
                | AP (a: cexp) (p: process)
                | PIf (b: bool) (p: process) (q: process)
                | PFix (p: process).

Definition memb := list process.
(*Fixpoint depth_cexp (e:cexp) : nat :=
   match e with CSKIP => 0
              | CLet x n e => 1 + depth_cexp e
              | CAppU l e => 0
              | CSeq e1 e2 => 1 + depth_cexp e1 + depth_cexp e2
              | CIf x e => 1 + depth_cexp e
              | Send _ _ => 0
              | Recv _ _ => 0
              | Paral e1 e2 => 1 + depth_cexp e1 + depth_cexp e2             
    end.
*)

Notation "p1 ; p2" := (CSeq p1 p2) (at level 50) : cexp_scope.

Notation "p1 [<-] p2" := (CAppU p1 p2) (at level 50) : cexp_scope.

