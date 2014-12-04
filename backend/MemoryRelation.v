Require Import Memory.
Require Import Values.

Set Implicit Arguments.


(* signature *)

Record MREL_ops (t:Type): Type := mkMREL_ops {
  sem :> t -> forall (m1 m2:mem), Prop;
  sem_value :> t -> forall (v1 v2:val), Prop;
  le: t -> t -> Prop;
  le_public: t -> t -> Prop
}.

Record MREL_props (t:Type) (ops:MREL_ops t): Prop := mkMREL_props {
  le_public_le:
    forall mrel1 mrel2 (Hle_public: ops.(le_public) mrel1 mrel2),
      ops.(le) mrel1 mrel2
}.

Record MREL: Type := mkMREL {
  t :> Type;
  ops: MREL_ops t;
  props: MREL_props ops
}.


(* equals *)

Definition MREL_ops_equals: MREL_ops unit :=
  mkMREL_ops
    (fun _ m1 m2 => m1 = m2)
    (fun _ v1 v2 => Val.lessdef v1 v2)
    (fun _ _ => True)
    (fun _ _ => True).

Program Definition MREL_props_equals: MREL_props MREL_ops_equals := mkMREL_props _ _.


(* extends *)

Definition MREL_ops_extends: MREL_ops unit :=
  mkMREL_ops
    (fun _ m1 m2 => Mem.extends m1 m2)
    (fun _ v1 v2 => Val.lessdef v1 v2)
    (fun _ _ => True)
    (fun _ _ => True).

Program Definition MREL_props_extends: MREL_props MREL_ops_extends := mkMREL_props _ _.


(* inject *)

Definition MREL_ops_inject: MREL_ops meminj :=
  mkMREL_ops
    Mem.inject
    val_inject
    inject_incr
    inject_incr.

Program Definition MREL_props_inject: MREL_props MREL_ops_inject := mkMREL_props _ _.
