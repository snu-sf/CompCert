Require Import Coqlib.
Require Import Relations.
Require Import sflib.

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

Inductive change_one (R: relation A):
  forall (tr: t) (tr': t), Prop :=
| change_one_base: forall r r' (REL: R r r'),
                          change_one R (Tree_singleton r) (Tree_singleton r')
| change_one_comp_left: forall r r' tr (TREL: change_one R r r'),
                               change_one R (Tree_composite r tr) (Tree_composite r' tr)
| change_one_comp_right: forall r r' tr (TREL: change_one R r r'),
                                change_one R (Tree_composite tr r) (Tree_composite tr r').

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

Lemma Tree_Forall2_split2 A B C
      (pred1 : A -> B -> Prop) (pred2 : B -> B -> Prop)
      (pred3 : B -> C -> Prop) (treeA : Tree.t A) (treeC : Tree.t C):
  Tree.Forall2
    (fun (a : A) (c : C) => exists (b1 b2:B), pred1 a b1 /\ pred2 b1 b2 /\ pred3 b2 c) treeA treeC <->
  (exists (treeB1 treeB2: Tree.t B),
     Tree.Forall2 pred1 treeA treeB1 /\ Tree.Forall2 pred2 treeB1 treeB2 /\ Tree.Forall2 pred3 treeB2 treeC).
Proof.
  intros.
  remember (fun a c => exists b1 b2, pred1 a b1 /\ pred2 b1 b2 /\ pred3 b2 c) as predA.
  remember (fun a c => exists b1, pred1 a b1 /\ exists b2, pred2 b1 b2 /\ pred3 b2 c) as predB.
  assert (pcomp: Tree.Forall2 predA treeA treeC <-> Tree.Forall2 predB treeA treeC).
  { apply Tree.Forall2_compat. subst. split; intros; des; eauto. }
  subst. rewrite -> pcomp.
  generalize (Tree.Forall2_split pred1 (fun b c => exists b2, pred2 b b2 /\ pred3 b2 c) treeA treeC). intros. rewrite -> H.
  split; intros; des.
  - apply Tree.Forall2_split in H1. des. eauto.
  - exists treeB1. split; auto. apply Tree.Forall2_split. eauto.
Qed.

Lemma Forall2_eq A (tree1 tree2:t A) (HForall: Forall2 eq tree1 tree2):
  tree1 = tree2.
Proof.
  revert tree2 HForall. induction tree1; intros tree2 HForall; inv HForall; auto.
  f_equal.
  - apply IHtree1_1. auto.
  - apply IHtree1_2. auto.
Qed.

Lemma Tree_Forall2_eq_same X (tr: Tree.t X):
  Tree.Forall2 eq tr tr.
Proof.
  intros. induction tr; constructor; auto.
Qed.

Lemma Forall_reduce A (pred:A->Prop) (rA:A->A->option A)
      (H: forall a1 a2 a (Ha:rA a1 a2 = Some a) (H1:pred a1) (H2:pred a2),
          pred a)
      (treeA:t A) (a:A)
      (Hpred: Forall pred treeA)
      (Ha: reduce rA treeA = Some a):
    pred a.
Proof.
  revert a Ha Hpred. induction treeA; simpl; intros a Ha Hpred.
  { inv Ha. inv Hpred. auto. }
  inv Hpred.
  destruct (reduce rA treeA1) as [a1|] eqn:Ha1; [|inv Ha].
  destruct (reduce rA treeA2) as [a2|] eqn:Ha2; [|inv Ha].
  eapply H; eauto.
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

Lemma rtc_change_one_attach_left:
  forall A (tr1 tr1' tr2:t A) R (RTCTR: rtc (change_one R) tr1 tr1'),
    rtc (change_one R) (Tree_composite tr1 tr2) (Tree_composite tr1' tr2).
Proof.
  intros. induction RTCTR.
  - constructor. constructor. eauto.
  - econs 2.
  - econs 3; eauto.
Qed.

Lemma rtc_change_one_attach_right:
  forall A (tr1 tr2 tr2':t A) R (RTCTR: rtc (change_one R) tr2 tr2'),
    rtc (change_one R) (Tree_composite tr1 tr2) (Tree_composite tr1 tr2').
Proof.
  intros. induction RTCTR.
  - constructor. constructor. eauto.
  - econs 2.
  - econs 3; eauto.
Qed.

Lemma Tree_Forall2_rtc_rel_rtc_change_one:
  forall A (tr1 tr2: Tree.t A) (R: relation A)
         (FAR: Tree.Forall2 (rtc R) tr1 tr2),
    rtc (change_one R) tr1 tr2.
Proof.
  intros.
  induction FAR.
  - induction Hpred.
    + constructor. constructor. auto.
    + econs 2.
    + econs 3; eauto.
  - econs 3.
    + eapply rtc_change_one_attach_left. eauto.
    + eapply rtc_change_one_attach_right. eauto.
Qed.

Lemma Forall2_Forall A B (P:A->Prop) (ta:Tree.t A) (tb:Tree.t B)
      (H: Tree.Forall2 (fun a b => P a) ta tb):
  Tree.Forall (fun a => P a) ta.
Proof.
  generalize dependent tb.
  induction ta; intros; inv H; constructor; eauto.
Qed.

End Tree.
