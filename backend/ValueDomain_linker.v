Require Import Coqlib.
Require Import Zwf.
Require Import Maps.
Require Import Compopts.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Lattice.
Require Import Kildall.
Require Import Registers.
Require Import RTL.
Require Import ValueDomain.

Set Implicit Arguments.

Inductive romem_le (rm1 rm2:romem): Prop :=
| romem_le_intro
    (H: forall b ab (Hrm1: rm1 ! b = Some ab),
          rm2 ! b = Some ab)
.

Lemma romem_le_refl rm: romem_le rm rm.
Proof. constructor. intros. auto. Qed.

Lemma vge_loadv_rm
      prm rm (Hprm: romem_le prm rm)
      chunk am av:
  vge (loadv chunk prm am av) (loadv chunk rm am av).
Proof.
  admit.
Qed.

Lemma pge_loadbytes_rm
      prm rm (Hprm: romem_le prm rm)
      am ap:
  pge (loadbytes am prm ap) (loadbytes am rm ap).
Proof.
  admit.
Qed.
