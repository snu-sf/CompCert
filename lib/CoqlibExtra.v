Require Import Coqlib.
Require Import Errors.

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

Lemma list_norepet_option_map_find A (l:list (positive * A)) (var:positive):
  list_norepet (@map _ positive (@fst _ _) l) ->
  @option_map _ _ (@snd _ _)
              (find (fun id : positive * A => peq var (fst id)) (rev l)) =
  @option_map _ _ (@snd _ _)
              (find (fun id : positive * A => peq var (fst id)) l).
Proof.
  induction l; simpl; intros Hnor; auto.
  destruct a. simpl in *. inv Hnor.
  destruct (peq var p); subst; simpl.
  - rewrite in_rev, <- map_rev in H1.
    revert H1 IHl. generalize (rev l).
    induction l0; simpl; intros; auto.
    + destruct (peq p p); subst; simpl; auto.
      contradict n. auto.
    + destruct a0. simpl in *.
      destruct (peq p p0); simpl; subst; auto. 
      contradict H1. left. auto.
  - rewrite <- IHl; auto.
    induction (rev l); simpl; auto.
    + destruct (peq var p); simpl; subst; auto.
      contradict n. auto.
    + destruct a0. simpl in *.
      destruct (peq var p0); simpl; subst; auto.
Qed.

Lemma strong_nat_ind:
  forall P : nat -> Prop,
    (forall n : nat, (forall k : nat, (k < n -> P k)%nat) -> P n) ->
    forall n : nat, P n.
Proof.
  intros P H.
  assert (forall n, (forall k, k < n -> P k)%nat).
  - induction n; intros k Hk.
    + inversion Hk.
    + apply Lt.le_lt_or_eq in Hk. destruct Hk as [Hk|Hk].
      * apply Lt.lt_S_n in Hk. apply IHn. auto.
      * inversion_clear Hk. apply H. apply IHn.
  - intros. eapply H0. eauto.
Qed.

Lemma OK_eq_inversion A (a b:A):
  OK a = OK b -> a = b.
Proof. intro. inv H. auto. Qed.

Ltac sig_clarify :=
  repeat match goal with
           | [H: context[if ?b then _ else _]|- _] =>
             let X := fresh "X" in destruct b eqn:X
           | [H: context[match ?b with OK _ => _ | Error _ => _ end]|- _] =>
             let X := fresh "X" in destruct b
           | [H: context[match ?b with Some _ => _ | None => _ end]|- _] =>
             let X := fresh "X" in destruct b
           | [H: bind _ _ = OK _ |- _] => monadInv H
           | [H: OK _ = OK _ |- _] => apply OK_eq_inversion in H; subst
           | [H: OK _ = Error _ |- _] => inv H
           | [H: Error _ = OK _ |- _] => inv H
           | [H: Some _ = Some _ |- _] => inv H
           | [H: Some _ = None _ |- _] => inv H
           | [H: None = Some _ |- _] => inv H
           | [H: inl _ = inl _ |- _] => inv H
           | [H: inl _ = inr _ |- _] => inv H
           | [H: inr _ = inl _ |- _] => inv H
           | [H: inr _ = inr _ |- _] => inv H
         end.
