Require Import Coqlib.

Set Implicit Arguments.

Module Tree.

Section DEF.

Variable (A:Type).
Inductive t' :=
| Tree_singleton (elt:A)
| Tree_composite (tree1 tree2:t')
.
Definition t := t'.

Inductive Forall (pred:forall (elt:A), Prop): forall (tree:t), Prop :=
| Forall_singleton elt (Helt: pred elt):
    Forall pred (Tree_singleton elt)
| Forall_composite tree1 tree2
                   (H1: Forall pred tree1) (H2: Forall pred tree2):
    Forall pred (Tree_composite tree1 tree2)
.

Lemma Forall_compat pred1 pred2 (Hpred: forall elt, pred1 elt <-> pred2 elt) t:
  Forall pred1 t <-> Forall pred2 t.
Proof.
  induction t; constructor; intro X; inv X; constructor;
  (try apply Hpred; auto);
  (try apply IHt1; auto);
  (try apply IHt2; auto).
Qed.

Fixpoint reduce (r:forall (elt1 elt2:A), option A) (tree:t): option A :=
  match tree with
    | Tree_singleton elt => Some elt
    | Tree_composite tree1 tree2 =>
      match reduce r tree1, reduce r tree2 with
        | Some elt1, Some elt2 => r elt1 elt2
        | _, _ => None
      end
  end.

End DEF.

Fixpoint map A B (f:forall (elt:A), B) (tree:t A): t B :=
  match tree with
    | Tree_singleton elt => Tree_singleton (f elt)
    | Tree_composite tree1 tree2 => Tree_composite (map f tree1) (map f tree2)
  end.

Inductive Forall2 A B (pred:forall (a:A) (b:B), Prop): forall (treeA:t A) (treeB:t B), Prop :=
| Forall2_singleton a b (Hpred: pred a b):
    Forall2 pred (Tree_singleton a) (Tree_singleton b)
| Forall2_composite a1 a2 b1 b2
                    (H1: Forall2 pred a1 b1)
                    (H2: Forall2 pred a2 b2):
    Forall2 pred (Tree_composite a1 a2) (Tree_composite b1 b2)
.

Lemma Forall2_compat A B (pred1 pred2:A->B->Prop) (Hpred: forall a b, pred1 a b <-> pred2 a b) t1 t2:
  Forall2 pred1 t1 t2 <-> Forall2 pred2 t1 t2.
Proof.
  revert t2. induction t1; intro t2; constructor; intro X; inv X; constructor;
  (try apply Hpred; auto);
  (try apply IHt1_1; auto);
  (try apply IHt1_2; auto).
Qed.

Lemma Forall2_implies A B (pred1 pred2:A->B->Prop) (Hpred: forall a b, pred1 a b -> pred2 a b) t1 t2:
  Forall2 pred1 t1 t2 -> Forall2 pred2 t1 t2.
Proof.
  revert t2. induction t1; intros t2 X; inv X; constructor;
  (try apply Hpred; auto);
  (try apply IHt1_1; auto);
  (try apply IHt1_2; auto).
Qed.

Lemma Forall2_split A B C
      (pred1:A->B->Prop) (pred2:B->C->Prop)
      (treeA:t A) (treeC:t C):
  Forall2 (fun a c => exists b, pred1 a b /\ pred2 b c) treeA treeC <->
  exists treeB,
    Forall2 pred1 treeA treeB /\ Forall2 pred2 treeB treeC.
Proof.
  revert treeC. induction treeA; intro treeC; constructor; intro X.
  - inv X. destruct Hpred as [? [? ?]]. eexists. split; econstructor; eauto.
  - destruct X as [? [? ?]]. inv H. inv H0. constructor. eexists. split; eauto.
  - inv X. apply IHtreeA1 in H3. apply IHtreeA2 in H4.
    destruct H3 as [? [? ?]]. destruct H4 as [? [? ?]].
    eexists. split; econstructor; eauto.
  - destruct X as [? [? ?]]. inv H. inv H0. constructor.
    + apply IHtreeA1. eexists. split; eauto.
    + apply IHtreeA2. eexists. split; eauto.
Qed.

Lemma Forall2_eq A (tree1 tree2:t A) (HForall: Forall2 eq tree1 tree2):
  tree1 = tree2.
Proof.
  revert tree2 HForall. induction tree1; intros tree2 HForall; inv HForall; auto.
  f_equal.
  - apply IHtree1_1. auto.
  - apply IHtree1_2. auto.
Qed.

Lemma Forall2_reduce A B (pred:A->B->Prop) (rA:A->A->option A) (rB:B->B->option B)
      (H: forall a1 a2 a b1 b2 (Ha:rA a1 a2 = Some a) (H1:pred a1 b1) (H2:pred a2 b2),
          exists b, rB b1 b2 = Some b /\ pred a b)
      (treeA:t A) (treeB:t B) (a:A)
      (Hpred: Forall2 pred treeA treeB)
      (Ha: reduce rA treeA = Some a):
  exists b,
    reduce rB treeB = Some b /\
    pred a b.
Proof.
  revert a Ha treeB Hpred. induction treeA; simpl; intros a Ha treeB Hpred.
  { inv Ha. inv Hpred. eexists. split; eauto; auto. }
  inv Hpred.
  destruct (reduce rA treeA1) as [a1|] eqn:Ha1; [|inv Ha].
  destruct (reduce rA treeA2) as [a2|] eqn:Ha2; [|inv Ha].
  eapply IHtreeA1 in H0; eauto. eapply IHtreeA2 in H4; eauto.
  destruct H0 as [? [? ?]]. destruct H4 as [? [? ?]].
  simpl. rewrite H0, H2. eapply H; eauto.
Qed.

End Tree.
