(* *********************************************************************)
(*                                                                     *)
(*                   Viktor and Gil's lemmas & tactic                  *)
(*                                                                     *)
(* *********************************************************************)

(** This file collects a number of basic lemmas and tactics for better
    proof automation, structuring large proofs, or rewriting.  Most of 
    the rewriting support is ported from ss-reflect. *)

(** Symbols starting with [vlib__] are internal. *)

Require Import Bool Arith ZArith String Program.
Require Import Relations.
(* Require Export paconotation. *)
(* Require Export newtac. *)

Set Implicit Arguments.

Hint Unfold not iff id.

(* ************************************************************************** *)
(** * Coersion of [bool] into [Prop] *)
(* ************************************************************************** *)

(** Coersion of bools into Prop *)
Coercion is_true (b : bool) : Prop := b = true.

(** Hints for auto *)
Lemma vlib__true_is_true : true.
Proof. reflexivity. Qed.

Lemma vlib__not_false_is_true : ~ false.
Proof. discriminate. Qed.

Lemma vlib__negb_rewrite: forall {b}, negb b -> b = false.
Proof. intros []; (reflexivity || discriminate). Qed.

Lemma vlib__andb_split: forall {b1 b2}, b1 && b2 -> b1 /\ b2.
Proof. intros [] []; try discriminate; auto. Qed.

Hint Resolve vlib__true_is_true vlib__not_false_is_true.

(* ************************************************************************** *)
(** * Basic automation tactics *)
(* ************************************************************************** *)

(** Set up for basic simplification *)

Create HintDb vlib discriminated.

(** Adaptation of the ss-reflect "[done]" tactic. *)

Ltac vlib__basic_done :=
  solve [trivial with vlib | apply sym_equal; trivial | discriminate | contradiction].

Ltac done := unfold not in *; trivial with vlib; hnf; intros;
  solve [try vlib__basic_done; split;
         try vlib__basic_done; split;
         try vlib__basic_done; split;
         try vlib__basic_done; split;
         try vlib__basic_done; split; vlib__basic_done
    | match goal with H : ~ _ |- _ => solve [case H; trivial] end].

Tactic Notation "by"  tactic(tac) := (tac; done).

Ltac vlib__complaining_inj f H :=
  let X := fresh in
  (match goal with | [|- ?P ] => set (X := P) end);
  injection H;
  (lazymatch goal with | [ |- f _ = f _ -> _] => fail | _ => idtac end);
  clear H; intros;
  subst X;
  try subst.

Ltac vlib__clarify1 :=
  try subst;
  repeat match goal with
  | [H: is_true (andb _ _) |- _] => case (vlib__andb_split H); clear H; intros ? H
  | [H: is_true (negb ?x) |- _] => rewrite (vlib__negb_rewrite H) in *
  | [H: is_true ?x        |- _] => rewrite H in *
  | [H: ?x = true         |- _] => rewrite H in *
  | [H: ?x = false        |- _] => rewrite H in *
  | [H: ?f _             = ?f _             |- _] => vlib__complaining_inj f H
  | [H: ?f _ _           = ?f _ _           |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _         = ?f _ _ _         |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _       = ?f _ _ _ _       |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _ _     = ?f _ _ _ _ _     |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _ _ _   = ?f _ _ _ _ _ _   |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _ _ _ _ = ?f _ _ _ _ _ _ _ |- _] => vlib__complaining_inj f H
  end; try done.

(** Perform injections & discriminations on all hypotheses *)

Ltac clarify :=
  vlib__clarify1;
  repeat match goal with
    | H1: ?x = Some _, H2: ?x = None   |- _ => rewrite H2 in H1; vlib__clarify1
    | H1: ?x = Some _, H2: ?x = Some _ |- _ => rewrite H2 in H1; vlib__clarify1
  end.

Definition  NW A (P: () -> A) : A := P ().

Notation "<< x : t >>" := (NW (fun x => t)) (at level 80, x ident, no associativity).

Hint Unfold NW.

Ltac des1 :=
  match goal with
    | H : NW _ |- _ => red in H
    | H : exists x, NW (fun y => _) |- _ =>
      let x' := fresh x in let y' := fresh y in destruct H as [x' y']; red in y'
    | H : exists x, ?p |- _ =>
      let x' := fresh x in destruct H as [x' H]
    | H : ?p /\ ?q |- _ =>
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => fresh H end in
      destruct H as [x' y'];
      match p with | NW _ => red in x' | _ => idtac end;
      match q with | NW _ => red in y' | _ => idtac end
    | H : ?p <-> ?q |- _ =>
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => fresh H end in
      destruct H as [x' y'];
      match p with | NW _ => unfold NW at 1 in x'; red in y' | _ => idtac end;
      match q with | NW _ => unfold NW at 1 in y'; red in x' | _ => idtac end
    | H : ?p \/ ?q |- _ =>
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => H end in
      destruct H as [x' | y'];
      [ match p with | NW _ => red in x' | _ => idtac end
      | match q with | NW _ => red in y' | _ => idtac end]
  end.

Ltac des := repeat des1.

Ltac splits :=
  intros; unfold NW;
  repeat match goal with
  | [ |- _ /\ _ ] => split
  end.
Ltac esplits :=
  intros; unfold NW;
  repeat match goal with
  | [ |- @ex _ _ ] => eexists
  | [ |- _ /\ _ ] => split
  | [ |- @sig _ _ ] => eexists
  | [ |- @sigT _ _ ] => eexists
  | [ |- @prod _  _ ] => split
  end.

Tactic Notation "econs" := econstructor.
Tactic Notation "econs" int_or_var(x) := econstructor x.
Tactic Notation "i" := intros.
Tactic Notation "ii" := repeat intro.

Notation rtc := (clos_refl_trans _).
Hint Immediate rt_step Relation_Operators.rt_refl Relation_Operators.t_step.

(* (* from paconotation *) *)

Notation "p <0= q" :=
  (forall (PR: p : Prop), q : Prop)
  (at level 50, no associativity, only parsing).

Notation "p <1= q" :=
  (forall x0 (PR: p x0 : Prop), q x0 : Prop)
  (at level 50, no associativity).

Notation "p <2= q" :=
  (forall x0 x1 (PR: p x0 x1 : Prop), q x0 x1 : Prop)
  (at level 50, no associativity).

Notation "p <3= q" :=
  (forall x0 x1 x2 (PR: p x0 x1 x2 : Prop), q x0 x1 x2 : Prop)
  (at level 50, no associativity).