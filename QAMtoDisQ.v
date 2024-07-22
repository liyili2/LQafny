Require Import DisQDef.
Require Import DisQType.
Require Import DisQSyntax.
Require Import QAM.

(*work in progress*)
Fixpoint QAMtoDisqTranslation (a: config) : (config) * (qstate)(*input is not qam_sem*)
  := match a with
  | 