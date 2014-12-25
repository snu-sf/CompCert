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
    (fun _ v1 v2 => v1 = v2)
    (fun _ _ => True)
    (fun _ _ => True)
    (fun _ _ _ _ _ => tt).

Program Definition mrelT_props_equals: mrelT_propsT mrelT_ops_equals := mkmrelT_propsT _ _ _ _ _ _.
Next Obligation. repeat constructor. Qed.
Next Obligation. repeat constructor. Qed.

Lemma mrelT_ops_equals_list_equal mrel v1 v2:
  v1 = v2 <-> list_forall2 (mrelT_ops_equals.(sem_value) mrel) v1 v2.
Proof.
  revert v2.
  induction v1; intros; constructor; intro H; inv H; simpl; try constructor; auto.
  - apply IHv1. auto.
  - inv H2. f_equal. apply IHv1. auto.
Qed.

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
Structure mrelT_inject: Type := mkmrelT_inject {
  mrelT_meminj:> meminj;
  mrelT_src: mem;
  mrelT_tgt: mem
}.

Inductive mrelT_sem (mrel:mrelT_inject) (m_src m_tgt:mem): Prop :=
| mrelT_sem_intro
    (Hinject: Mem.inject mrel.(mrelT_meminj) m_src m_tgt)
    (Hsrc: mrel.(mrelT_src) = m_src)
    (Htgt: mrel.(mrelT_tgt) = m_tgt)
.

Inductive mrelT_le (mrel1 mrel2:mrelT_inject): Prop :=
| mrelT_le_intro
    (INCR: inject_incr mrel1.(mrelT_meminj) mrel2.(mrelT_meminj))
    (LE: Ple (Mem.nextblock mrel1.(mrelT_tgt)) (Mem.nextblock mrel2.(mrelT_tgt)))
    (INJ: forall b1 b2 delta, 
          mrel2.(mrelT_meminj) b1 = Some(b2, delta) -> Plt b2 (Mem.nextblock mrel1.(mrelT_tgt)) -> mrel1.(mrelT_meminj) b1 = Some(b2, delta))
    (PERM1: forall b1 b2 delta ofs,
          mrel2.(mrelT_meminj) b1 = Some(b2, delta) -> Plt b2 (Mem.nextblock mrel1.(mrelT_tgt)) ->
          Mem.perm mrel2.(mrelT_src) b1 ofs Max Nonempty -> Mem.perm mrel1.(mrelT_src) b1 ofs Max Nonempty)
    (PERM2: forall b ofs, Plt b (Mem.nextblock mrel1.(mrelT_tgt)) ->
          Mem.perm mrel1.(mrelT_tgt) b ofs Cur Freeable -> Mem.perm mrel2.(mrelT_tgt) b ofs Cur Freeable)
    (PERM3: forall b ofs k p, Plt b (Mem.nextblock mrel1.(mrelT_tgt)) ->
          Mem.perm mrel2.(mrelT_tgt) b ofs k p -> Mem.perm mrel1.(mrelT_tgt) b ofs k p)
.

Program Instance PreOrder_mrelT_le: PreOrder mrelT_le.
Next Obligation. constructor; intros; auto. reflexivity. Qed.
Next Obligation.
  repeat intro. inv H. inv H0. constructor; intros; auto.
  - eapply inject_incr_trans; eauto.
  - rewrite LE. auto.
  - eapply INJ; eauto. eapply INJ0; eauto.
    eapply Plt_Ple_trans; eauto.
  - eapply PERM1; eauto. eapply INJ0; eauto.
    eapply Plt_Ple_trans; eauto.
    eapply PERM0; eauto.
    eapply Plt_Ple_trans; eauto.
  - eapply PERM4; eauto.
    eapply Plt_Ple_trans; eauto.
  - eapply PERM3; eauto. eapply PERM5; eauto.
    eapply Plt_Ple_trans; eauto.
Qed.

Definition mrelT_ops_inject: mrelT_opsT mrelT_inject :=
  mkmrelT_opsT
    mrelT_sem
    (fun mrel => val_inject mrel.(mrelT_meminj))
    (fun _ _ => True)
    mrelT_le
    (fun _ _ _ m _ => mkmrelT_inject (Mem.flat_inj (Mem.nextblock m)) m m).

Program Definition mrelT_props_inject: mrelT_propsT mrelT_ops_inject := mkmrelT_propsT _ _ _ _ _ _.
Next Obligation. constructor; auto. Qed.
Next Obligation. inv H. auto. Qed.
Next Obligation.
  constructor; auto. simpl.
  eapply Genv.initmem_inject; eauto.
Qed.

Lemma mrelT_ops_inject_list_inject mrel v1 v2:
  val_list_inject mrel.(mrelT_meminj) v1 v2 <-> list_forall2 (mrelT_ops_inject.(sem_value) mrel) v1 v2.
Proof.
  revert v2.
  induction v1; intros; constructor; intro H; inv H; constructor; auto.
  - apply IHv1. auto.
  - apply IHv1. auto.
Qed.
