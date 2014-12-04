Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import WFType.

Set Implicit Arguments.

Section INDEXED_STEPS.

Variable genv: Type.
Variable state: Type.

Variable step: genv -> state -> trace -> state -> Prop.

Inductive indexed_step (ge: genv): Indexed.t state -> trace -> Indexed.t state -> Prop :=
| indexed_step_index
    i1 i2 st (Hi: WF.rel i2 i1):
    indexed_step ge (Indexed.mk i1 st) E0 (Indexed.mk i2 st)
| indexed_step_step
    i1 i2 st1 evt st2 (Hstep: step ge st1 evt st2):
    indexed_step ge (Indexed.mk i1 st1) evt (Indexed.mk i2 st2)
.

End INDEXED_STEPS.
