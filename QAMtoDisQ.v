Require Import DisQDef.
Require Import DisQSyntax.
Require Import QAM.
Require Import Coq.FSets.FMapList.
Require Import List.
Import ListNotations.
(*work in progress*)
(* Fixpoint QAMtoDisqTranslation (a: config) : (config) * (qstate)(*input is not qam_sem*)
  := match a with
  | CtxM u v => NewCMemb (QAMtoDisqTranslation u) (QAMtoDisqTranslation v)
  end. *)

(* Fixpoint ProcessTranslation (p: QAM.process) : (DisQSyntax.process)
:= match p with
| Nil => PNil
| AR a r => AP (ActionTranslation a) (ProcessTranslation r)
| Choice p r =>
| Rept r =>
end. *)
Parameter cmess_translated: cmess -> aexp.
Local Open Scope nat_scope.

Definition ActionTranslation (a: QAM.action) (n: nat): (DisQSyntax.process)
:= match a with
| CSend cc cm => DP (Send cc (cmess_translated cm)) PNil
| CcRecv cc x => DP (Recv cc x) PNil
| CqRecv qc x => DP (Recv qc x) PNil
| Encode c m => match is_class m with 
    | true => AP (CAppU ((c, (BNum 0), (BVar n 0))::nil) (RZ 1 c (Num 0))) PNil
    | false => SQIR.CNOT SQIR.H
    end
| Decode c m => match is_class m with 
    | true => SQIR.CNOT SQIR.H Meas m
    | false => Meas m
    end
end.

Fixpoint MembraneTranslation (m: QAM.memb) : (DisQSyntax.process)
:= match m with 
| CtxM r phi =>
| ALock r t =>
| ActM p c Q =>
end.

Fixpoint ConfigTranslation (q: config) : (DisQSyntax.process)
| match m with 
| a::b => 
