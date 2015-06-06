Require Import Axioms.
Require Import Coqlib.
Require Import AST.

Module WF.
  Structure t: Type := mk {
    A: Type;
    R: A -> A -> Prop;
    _wf: well_founded R;
    a: A
  }.

  Inductive rel: t -> t -> Prop :=
  | _rel
      A (R:A -> A -> Prop) _wf a b (H: R a b):
      rel (mk A R _wf a) (mk A R _wf b)
  .

  Lemma wf: well_founded rel.
  Proof.
    intro a. destruct a as [A R _wf a].
    generalize (_wf a). induction 1.
    constructor. intros. inv H1.
    apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H5.
    apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H6.
    subst.
    rewrite (proof_irr _wf1 _wf).
    apply H0. auto.
  Qed.

  Definition from_nat (n:nat): WF.t :=
    WF.mk _ _ lt_wf n.

  Definition from_positive (p:positive): WF.t :=
    WF.mk _ _ Plt_wf p.

  Definition elt: t := from_positive 1%positive.
End WF.

Module Indexed.
  Structure t (T:Type): Type := mk {
    index: WF.t;
    elt: T
  }.

  Arguments mk {T} _ _.
  Arguments index {T} _.
  Arguments elt {T} _.
End Indexed.
