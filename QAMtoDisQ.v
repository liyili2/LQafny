Require Import DisQDef.
Require Import DisQSyntax.
Require Import QAM.
Require Import SQIR.

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
Definition ActionTranslation (a: QAM.action) : (DisQSyntax.process)
:= match a with
| CSend cc cm => DP (Send cc (cmess_translated cm)) PNil
| CcRecv cc x => DP (Recv cc x) PNil
| CqRecv qc x => DP (Recv qc x) PNil
| LEncode q mu x => AP (SQIR.X SQIR.CZ q) PNil
| LDecode q x => AP (CMeas x q) PNil
| GEncode c x => AP (H CNOT) PNil
| GDecode c x => AP (Meas x) PNil
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
