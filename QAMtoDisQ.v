Require Import DisQDef.
Require Import DisQType.
Require Import QAM.

(*work in progress*)
Fixpoint QAMtoDisqTranslation (a: qam_sem) : Prop := 
    match a with
    | True => QAMtoDisqTranslation(~a)
    | False => False
    end.