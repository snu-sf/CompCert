Require Import Equivalence EquivDec.
Require Import Coqlib CoqlibExtra.
Require Import Maps.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Set Implicit Arguments.

Definition PTree_unelements (A : Type) (l : list (PTree.elt * A)) : PTree.t A :=
  List.fold_left
    (fun acc kv => PTree.set (fst kv) (snd kv) acc)
    l
    (PTree.empty _).

Lemma PTree_gespec {A:Type} (m:PTree.t A) (i:positive):
  PTree.get i m = option_map snd (find (fun id => peq i (fst id)) (PTree.elements m)).
Proof.
  generalize (PTree.elements_correct m i).
  generalize (PTree.elements_complete m i).
  generalize (PTree.get i m).
  generalize (PTree.elements m).
  induction l; intros v H1 H2; simpl.
  - destruct v;[|auto].
    exploit H2; eauto.
    intro X. inv X.
  - destruct a. simpl in *. destruct (peq i p); [subst|]; simpl.
    + apply H1. left. auto.
    + apply IHl; auto.
      * intros. exploit H2; eauto.
        intros [X|X]; auto.
        contradict n. inv X. auto.
Qed.

Lemma PTree_guespec {A:Type} (l:list (positive * A)) (i:positive):
  PTree.get i (PTree_unelements l) = option_map snd (find (fun id => peq i (fst id)) (rev l)).
Proof.
  unfold PTree_unelements. rewrite <- fold_left_rev_right.
  induction (rev l); simpl.
  - rewrite PTree.gempty. auto.
  - rewrite PTree.gsspec. destruct a. simpl in *.
    destruct (peq i p); simpl in *; subst; auto.
Qed.

Lemma PTree_unelements_elements A (m:PTree.t A) b:
  PTree.get b (PTree_unelements (PTree.elements m)) = PTree.get b m.
Proof.
  rewrite PTree_guespec, PTree_gespec.
  generalize (PTree.elements_keys_norepet m).
  apply list_norepet_option_map_find.
Qed.

Fixpoint PTree_xoption_map (A B : Type) (f : positive -> A -> option B) (m : PTree.t A) (i : positive)
         {struct m} : PTree.t B :=
  match m with
    | PTree.Leaf => PTree.Leaf
    | PTree.Node l o r =>
      PTree.Node
        (PTree_xoption_map f l (xO i))
        (match o with
           | None => None
           | Some x => f (PTree.prev i) x
         end)
        (PTree_xoption_map f r (xI i))
  end.

Definition PTree_option_map (A B : Type) (f : positive -> A -> option B) m := PTree_xoption_map f m xH.

Lemma PTree_xgoption_map:
  forall (A B: Type) (f: positive -> A -> option B) (i j : positive) (m: PTree.t A),
    PTree.get i (PTree_xoption_map f m j) = match PTree.get i m with
                                              | None => None
                                              | Some x => f (PTree.prev (PTree.prev_append i j)) x
                                            end.
Proof.
  induction i; intros; destruct m; simpl; auto.
Qed.

Theorem PTree_goption_map:
  forall (A B: Type) (f: positive -> A -> option B) (i: positive) (m: PTree.t A),
    PTree.get i (PTree_option_map f m) = match PTree.get i m with
                                           | None => None
                                           | Some x => f i x
                                         end.
Proof.
  intros A B f i m.
  unfold PTree_option_map.
  rewrite PTree_xgoption_map. destruct (PTree.get i m); auto. repeat f_equal. exact (PTree.prev_involutive i).
Qed.

Inductive PTree_le A (m1 m2:PTree.t A): Prop :=
| PTree_le_intro
    (H: forall b ab (Hrm1: m1 ! b = Some ab),
          m2 ! b = Some ab)
.

Program Instance PTree_le_PreOrder A: PreOrder (@PTree_le A).
Next Obligation.
  constructor. intros. auto.
Qed.
Next Obligation.
  repeat intro. inv H. inv H0. constructor. intros.
  exploit H1; eauto.
Qed.

Inductive PTree_eq A (m1 m2:PTree.t A): Prop :=
| PTree_eq_intro
    (H: forall i : positive, m1 ! i = m2 ! i)
.

Program Instance PTree_eq_Equivalence A: Equivalence (@PTree_eq A).
Next Obligation. constructor. intros. auto. Qed.
Next Obligation. constructor. inv H. symmetry. auto. Qed.
Next Obligation. constructor. inv H. inv H0. intros. rewrite H1. auto. Qed.

Lemma PTree_elements_extensional' A (m1 m2:PTree.t A)
      (H: PTree_eq m1 m2):
  PTree.elements m1 = PTree.elements m2.
Proof. inv H. apply PTree.elements_extensional. auto. Qed.

Lemma PTree_unelements_elements' A (m:PTree.t A):
  PTree_eq m (PTree_unelements (PTree.elements m)).
Proof. constructor. intro. rewrite PTree_unelements_elements. auto. Qed.

Lemma PTree_combine_morphism
      A B C (f:option A -> option B -> option C)
      (Hf: f None None = None)
      m1 m2 m1' m2'
      (H1: PTree_eq m1 m1') (H2: PTree_eq m2 m2'):
  PTree_eq (PTree.combine f m1 m2) (PTree.combine f m1' m2').
Proof.
  constructor. intro. rewrite ? PTree.gcombine; auto.
  inv H1. inv H2. rewrite H. rewrite H0. auto.
Qed.

Lemma PTree_Properties_for_all_morphism
      A (f:PTree.elt -> A -> bool)
      m1 m2 (Hm: PTree_eq m1 m2):
  PTree_Properties.for_all m1 f = PTree_Properties.for_all m2 f.
Proof.
  inv Hm.
  destruct (PTree_Properties.for_all m1 f) eqn:H1.
  - symmetry. apply PTree_Properties.for_all_correct. intros.
    rewrite <- H in H0. eapply PTree_Properties.for_all_correct in H1; eauto.
  - apply PTree_Properties.for_all_false in H1. destruct H1 as [? [? [? ?]]].
    symmetry. apply PTree_Properties.for_all_false. eexists. eexists. split; eauto.
    rewrite <- H. auto.
Qed.

Lemma PTree_option_map_morphism
      A B (f: positive -> A -> option B)
      m1 m2 (Hm: PTree_eq m1 m2):
  PTree_eq (PTree_option_map f m1) (PTree_option_map f m2).
Proof.
  constructor. intro. rewrite ? PTree_goption_map.
  inv Hm. rewrite H. auto.
Qed.

Inductive PTree_rel {A B} (rel:A->B->Prop) (mA:PTree.t A) (mB:PTree.t B): Prop :=
| PTree_rel_intro
    (H: forall i : positive,
          match mA ! i, mB ! i with
            | Some bA, Some bB => rel bA bB
            | None, None => True
            | _, _ => False
          end)
.

Lemma list_forall2_PTree_unelements A B
      (R:A->B->Prop) (p:list (positive*A)) (q:list (positive*B))
      (H: list_forall2 (fun g1 g2 => fst g1 = fst g2 /\ R (snd g1) (snd g2)) p q):
  PTree_rel
    R
    (PTree_unelements p)
    (PTree_unelements q).
Proof.
  constructor. intro. rewrite ? PTree_guespec.
  apply list_forall2_rev in H. revert H.
  simpl in *. generalize (rev p) (rev q).
  induction l; intros l0 H; inv H; simpl; auto.
  destruct a. simpl. destruct (peq i p0); subst; simpl.
  - destruct b1, H2 as [? ?]. simpl in *. subst.
    destruct (peq p1 p1); simpl; [|xomega]. auto.
  - destruct b1, H2 as [? ?]. simpl in *. subst.
    destruct (peq i p1); simpl; [xomega|].
    apply IHl. auto.
Qed.

Lemma PTree_rel_PTree_elements A B
      (R:A->B->Prop) p q
      (H: PTree_rel R p q):
  list_forall2
    (fun g1 g2 => fst g1 = fst g2 /\ R (snd g1) (snd g2))
    (PTree.elements p) (PTree.elements q).
Proof.
  exploit (PTree.elements_canonical_order R p q).
  - intros. inv H. specialize (H1 i). rewrite H0 in H1.
    destruct (q ! i); [|inv H1]. eexists. split; auto.
  - intros. inv H. specialize (H1 i). rewrite H0 in H1.
    destruct (p ! i); [|inv H1]. eexists. split; auto.
  - generalize (PTree.elements p) (PTree.elements q). clear p q H.
    induction l; intros l0 X; inv X; constructor; auto.
Qed.
