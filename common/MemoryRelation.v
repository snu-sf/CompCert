Require Import RelationClasses.
Require Import Coqlib.
Require Import Memory.
Require Import Values.
Require Import Globalenvs AST.

Set Implicit Arguments.

(* signature *)

Record mrelT_opsT (t:Type): Type := mkmrelT_opsT {
  sem :> t -> forall (m1 m2:mem), Prop;
  sem_value :> t -> forall (v1 v2:val), Prop;
  le: t -> t -> Prop;
  le_public: t -> t -> Prop;
  mrel_init:
    forall F V (prog:program F V) m (Hm: Genv.init_mem prog = Some m), t
}.

Record mrelT_propsT (t:Type) (ops:mrelT_opsT t): Prop := mkmrelT_propsT {
  le_preorder: PreOrder ops.(le);
  le_public_preorder: PreOrder ops.(le_public);
  le_public_le:
    forall mrel1 mrel2 (Hle_public: ops.(le_public) mrel1 mrel2),
      ops.(le) mrel1 mrel2;
  sem_value_int:
    forall mrel i v (H: ops.(sem_value) mrel (Vint i) v),
      v = Vint i;
  mrel_init_prop:
    forall F V (prog:AST.program F V) m (Hm: Genv.init_mem prog = Some m),
      ops.(sem) (ops.(mrel_init) prog Hm) m m
}.

Record mrelT: Type := mkmrelT {
  t :> Type;
  ops: mrelT_opsT t;
  props: mrelT_propsT ops
}.


(* equals *)

Definition mrelT_ops_equals: mrelT_opsT unit :=
  mkmrelT_opsT
    (fun _ m1 m2 => m1 = m2)
    (fun _ v1 v2 => Val.lessdef v1 v2)
    (fun _ _ => True)
    (fun _ _ => True)
    (fun _ _ _ _ _ => tt).

Program Definition mrelT_props_equals: mrelT_propsT mrelT_ops_equals := mkmrelT_propsT _ _ _ _ _ _.
Next Obligation. repeat constructor. Qed.
Next Obligation. repeat constructor. Qed.
Next Obligation. inv H. auto. Qed.

(* extends *)

Definition mrelT_ops_extends: mrelT_opsT unit :=
  mkmrelT_opsT
    (fun _ m1 m2 => Mem.extends m1 m2)
    (fun _ v1 v2 => Val.lessdef v1 v2)
    (fun _ _ => True)
    (fun _ _ => True)
    (fun _ _ _ _ _ => tt).

Program Definition mrelT_props_extends: mrelT_propsT mrelT_ops_extends := mkmrelT_propsT _ _ _ _ _ _.
Next Obligation. repeat constructor. Qed.
Next Obligation. repeat constructor. Qed.
Next Obligation. inv H. auto. Qed.
Next Obligation. apply Mem.extends_refl. Qed.

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
    inject_incr
    (fun _ _ _ m _ => Mem.flat_inj (Mem.nextblock m)).

Program Definition mrelT_props_inject: mrelT_propsT mrelT_ops_inject := mkmrelT_propsT _ _ _ _ _ _.
Next Obligation. constructor; repeat intro; auto. Qed.
Next Obligation. constructor; repeat intro; auto. Qed.
Next Obligation. inv H. auto. Qed.
Next Obligation. eapply Genv.initmem_inject; eauto. Qed.

Lemma mrelT_ops_inject_list_inject mrel v1 v2:
  val_list_inject mrel v1 v2 <-> list_forall2 (mrelT_ops_inject.(sem_value) mrel) v1 v2.
Proof.
  revert v2.
  induction v1; intros; constructor; intro H; inv H; constructor; auto.
  - apply IHv1. auto.
  - apply IHv1. auto.
Qed.
