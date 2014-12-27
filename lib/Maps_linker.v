Require Import Equivalence EquivDec.
Require Import Coqlib Coqlib_linker.
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
          