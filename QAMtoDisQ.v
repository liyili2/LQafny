Require Import DisQDef.
Require Import DisQType.
Require Import DisQSyntax.
Require Import QAM.
Require Import SQIR.

(*work in progress*)
(* Fixpoint QAMtoDisqTranslation (a: config) : (config) * (qstate)(*input is not qam_sem*)
  := match a with
  | CtxM u v => NewCMemb (QAMtoDisqTranslation u) (QAMtoDisqTranslation v)
  end. *)

Fixpoint ProcessTranslation (p: QAM.process) : (DisQSyntax.process)
:= match p with
| Nil => PNil
| AR a r => AP (ActionTranslation a) (ProcessTranslation r)
| Choice p r =>
| Rept r =>
end.

Definition ActionTranslation (a: QAM.action) : (DisQSyntax.process)
:= match a with
| CSend cc cm =>
| CcRecv cc x =>
| CqRecv qc x =>
| LEncode q mu x =>
| LDecode q x =>
| GEncode c x =>
| GDecode c x =>
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
