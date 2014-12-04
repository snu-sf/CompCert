Require Import Coqlib.

Set Implicit Arguments.

Definition unit_eq (v1 v2:unit): {v1 = v2} + {v1 <> v2}.
Proof. decide equality. Defined.

Definition is_empty (X:Type) (l:list X): bool :=
  match l with
    | nil => true
    | _ => false
  end.

Lemma list_forall2_rev (X Y:Type) (P: X -> Y -> Prop)
      (lx: list X) (ly: list Y) (H: list_forall2 P lx ly):
  list_forall2 P (rev lx) (rev ly).
Proof.
  generalize dependent ly. induction lx; intros; inv H.
  { constructor. }
  simpl. apply list_forall2_app; auto.
  repeat constructor; auto.
Qed.
