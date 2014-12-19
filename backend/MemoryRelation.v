Require Import Coqlib.
Require Import Memory.
Require Import Values.

Set Implicit Arguments.


(* signature *)

Record mrelT_opsT (t:Type): Type := mkmrelT_opsT {
  sem :> t -> forall (m1 m2:mem), Prop;
  sem_value :> t -> forall (v1 v2:val), Prop;
  le: t -> t -> Prop;
  le_public: t -> t -> Prop
}.

Record mrelT_props (t:Type) (ops:mrelT_opsT t): Prop := mkmrelT_props {
  le_public_le:
    forall mrel1 mrel2 (Hle_public: ops.(le_public) mrel1 mrel2),
      ops.(le) mrel1 mrel2
}.

Record mrelT: Type := mkmrelT {
  t :> Type;
  ops: mrelT_opsT t;
  props: mrelT_props ops
}.


(* equals *)

Definition mrelT_ops_equals: mrelT_opsT unit :=
  mkmrelT_opsT
    (fun _ m1 m2 => m1 = m2)
    (fun _ v1 v2 => Val.lessdef v1 v2)
    (fun _ _ => True)
    (fun _ _ => True).

Program Definition mrelT_props_equals: mrelT_props mrelT_ops_equals := mkmrelT_props _ _.


(* extends *)

Definition mrelT_ops_extends: mrelT_opsT unit :=
  mkmrelT_opsT
    (fun _ m1 m2 => Mem.extends m1 m2)
    (fun _ v1 v2 => Val.lessdef v1 v2)
    (fun _ _ => True)
    (fun _ _ => True).

Program Definition mrelT_props_extends: mrelT_props mrelT_ops_extends := mkmrelT_props _ _.

Lemma mrelT_ops_extends_lessdef_list mrel v1 v2:
  Val.lessdef_list v1 v2 <-> list_forall2 (mrelT_ops_extends.(sem_value) mrel) v1 v2.
Proof.
  revert v2.
  induction v1; intros; constructor; intro H; inv H; constructor; auto.
  - apply IHv1. auto.
  - apply IHv1. auto.
Qed.

(* inject *)

Definition mrelT_ops_inject: mrelT_opsT meminj :=
  mkmrelT_opsT
    Mem.inject
    val_inject
    inject_incr
    inject_incr.

Program Definition mrelT_props_inject: mrelT_props mrelT_ops_inject := mkmrelT_props _ _.
