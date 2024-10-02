Require Import DisQSyntax.
Require Import QAM.
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

Check [].
Definition ActionTranslation (a: QAM.action) (n: nat): (DisQSyntax.process)
:= match a with
| CSend cc cm => DP (Send cc (cmess_translated cm)) PNil
| CcRecv cc x => DP (Recv cc x) PNil
| CqRecv qc x => DP (Recv qc x) PNil
| Encode c m => match is_class m with 
    | true => AP (CAppU ((c, (BNum 0), (BNum n))::nil) (X c (Num 0))) (AP (CAppU ((c, (BNum 0), (BNum n))::nil) (RZ 1 c (Num 0))) PNil)
    | false => AP (CAppU ((c, (BNum 0), (BNum n))::nil) (H c (Num 0))) (AP (CAppU ((c, (BNum 0), (BNum n))::nil) (CU c (Num c) (X c (Num c)))) PNil)
    (* | false => AP (CAppU ((c, (BNum 0), (BVar n 0))::nil) (SQIR.CNOT 1 0)) (AP (CAppU ((c, (BNum 0), (BVar n 0))::nil) (SQIR.H c (Num 0))) PNil) *)
    end
| Decode c m => match is_class m with 
    | true => AP (CAppU ((c, (BNum 0), (BNum n))::nil) (H c (Num 0))) (AP (CAppU ((c, (BNum 0), (BNum n))::nil) (CU c (Num c) (X c (Num c)))) PNil)
    | false => AP (CMeas c ((c, (BNum 0), (BNum n))::nil)) PNil
    end
end.

(*Translate processes first
be smart about maybe changing the syntax a bit
how are you going to link action translation vs process translation
actions to processes; what should we translate QAM processes to?*)

Check [].
Definition SubProcessTranslation (p: QAM.subprocess): (DisQSyntax.process)
:= match p with
| Nil => PNil
| 
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
