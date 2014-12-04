Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_linker.
Require Import Maps_linker.
Require Import Integers Floats Values AST Globalenvs.
Require Import LinkerSpecification.

Set Implicit Arguments.


(* Future programs of a partial program after linkings *)
Section Linkeq.

Variable (F V:Type).  

(** `linkeq a b` means `b` is a possible future global definition of `a` after linkings *)

Definition globfun_linkeq (f1 f2:AST.fundef F): Prop :=
  f1 = f2 \/ globfun_linkable f1 f2.


Definition globvar_linkeq (v1 v2:globvar V): Prop :=
  v1 = v2 \/ globvar_linkable v1 v2.

Inductive globdef_linkeq: forall (g1 g2:globdef (AST.fundef F) V), Prop :=
| globdef_linkeq_fun
    f1 f2 (Hv: globfun_linkeq f1 f2):
    globdef_linkeq (Gfun f1) (Gfun f2)
| globdef_linkeq_var
    v1 v2 (Hv: globvar_linkeq v1 v2):
    globdef_linkeq (Gvar v1) (Gvar v2)
.

Definition globaldefs_linkeq (defs1 defs2:PTree.t (globdef (AST.fundef F) V)): Prop :=
  forall var def1 (Hsrc: PTree.get var defs1 = Some def1),
  exists def2,
    PTree.get var defs2 = Some def2 /\
    globdef_linkeq def1 def2.


(** `linkable` and `linkeq` properties *)

Program Instance globfun_linkeq_PreOrder: PreOrder globfun_linkeq.
Next Obligation.
  intro f. left. auto.
Qed.
Next Obligation.
  intros f1 f2 f3 H12 H23.
  destruct H12, H23; subst; auto.
  { left. auto. }
  { right. auto. }
  { right. auto. }
  inv H; inv H0.
  - right. apply globvar_linkable_ei.
  - right. apply globvar_linkable_ee.
Qed.

Lemma globdef_linkable_linkeq
      g1 g2 (Hlinkable: globdef_linkable g1 g2):
  globdef_linkeq g1 g2.
Proof.
  inv Hlinkable; constructor; auto.
  - right. auto.
  - right. auto.
Qed.

Program Instance globvar_linkeq_PreOrder: PreOrder globvar_linkeq.
Next Obligation.
  intros [info init readonly volatile].
  constructor; auto.
Qed.
Next Obligation.
  intros v1 v2 v3 H12 H23.
  destruct H12, H23; subst; auto.
  { left. auto. }
  { right. auto. }
  { right. auto. }
  right. inv H. inv H0.
  constructor; simpl.
  - rewrite Hinfo. auto.
  - destruct Hinit; subst; auto.
  - rewrite Hreadonly. auto.
  - rewrite Hvolatile. auto.
Qed.

Program Instance globdef_linkeq_PreOrder: PreOrder globdef_linkeq.
Next Obligation.
  intros [f|v]; constructor; reflexivity.
Qed.
Next Obligation.
  intros [f1|v1] [f2|v2] [f3|v3] H12 H23; inv H12; inv H23.
  - constructor. rewrite Hv. auto.
  - constructor. rewrite Hv. auto.
Qed.

End Linkeq.
