Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import Smallstep.
Require Import WFType.

Set Implicit Arguments.

Lemma semantics_compat
      stateT funT varT step
      (init1 init2: stateT -> Prop)
      (final1 final2: stateT -> int -> Prop)
      (ge: Genv.t funT varT)
      (Hinit: forall st, init1 st <-> init2 st)
      (Hfinal: forall st r, final1 st r <-> final2 st r):
  forward_simulation (Semantics step init1 final1 ge) (Semantics step init2 final2 ge).
Proof.
  eapply (Forward_simulation
            (Semantics step init1 final1 ge) (Semantics step init2 final2 ge)
            WF.wf
            (fun i st1 st2 => st1 = st2));
  simpl; intros.
  - exists WF.elt. eexists. split; auto. apply Hinit. auto.
  - subst. apply Hfinal. auto.
  - subst. exists WF.elt. eexists. split; auto. left. apply plus_one. auto.
  - auto.
Qed.
