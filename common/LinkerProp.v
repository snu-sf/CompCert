Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_linker.
Require Import Maps Maps_linker.
Require Import Integers Floats Values AST Globalenvs.
Require Import LinkerSpecification.
Require Import Errors.

Set Implicit Arguments.

Section LINKER_PROP.

Variable (fundefT F V:Type).
Variable (fundef_dec: fundef_decT fundefT F).
Variable (V_dec: forall (v1 v2:V), {v1 = v2} + {v1 <> v2}).

Lemma gflink_globdefs defs1 defs2 (Hlink: link_globdefs fundef_dec V_dec defs1 defs2 = None):
  exists var def1 def2,
    PTree.get var defs1 = Some def1 /\
    PTree.get var defs2 = Some def2 /\
    ~ globdef_linkable fundef_dec def1 def2 /\
    ~ globdef_linkable fundef_dec def2 def1.
Proof.
  unfold link_globdefs in Hlink.
  match goal with
    | [H: context[PTree_Properties.for_all ?m ?f] |- _] =>
      destruct (PTree_Properties.for_all m f) eqn:Hlinkable; inv Hlink
  end.
  apply PTree_Properties.for_all_false in Hlinkable.
  destruct Hlinkable as [i [x [Hx1 Hx2]]].
  destruct x; inv Hx2. rewrite PTree.gcombine in Hx1; auto.
  destruct (defs1 ! i) eqn:Hi1, (defs2 ! i) eqn:Hi2; inv Hx1.
  destruct (globdef_linkable_dec fundef_dec V_dec g g0); inv H0.
  destruct (globdef_linkable_dec fundef_dec V_dec g0 g); inv H1.
  repeat eexists; eauto.
Qed.

Lemma gtlink_globdefs defs1 defs2 defs (Hlink: link_globdefs fundef_dec V_dec defs1 defs2 = Some defs):
  forall var,
    match PTree.get var defs1, PTree.get var defs2, PTree.get var defs with
      | Some g1, Some g2, Some g =>
        (globdef_linkable fundef_dec g1 g2 /\ g2 = g) \/
        (globdef_linkable fundef_dec g2 g1 /\ g1 = g)
      | Some g1, None, Some g => g1 = g
      | None, Some g2, Some g => g2 = g
      | None, None, None => True
      | _, _, _ => False
    end.
Proof.
  intro i. unfold link_globdefs in Hlink.
  match goal with
    | [H: context[PTree_Properties.for_all ?m ?f] |- _] =>
      destruct (PTree_Properties.for_all m f) eqn:Hlinkable; inv Hlink
  end.
  rewrite PTree_goption_map, PTree.gcombine; auto.
  destruct (defs1 ! i) eqn:Hi1, (defs2 ! i) eqn:Hi2; auto.
  destruct (globdef_linkable_dec fundef_dec V_dec g g0).
  { left. split; auto. }
  destruct (globdef_linkable_dec fundef_dec V_dec g0 g).
  { right. split; auto. }
  eapply PTree_Properties.for_all_correct in Hlinkable; eauto.
  { instantiate (1 := None) in Hlinkable. inv Hlinkable. }
  instantiate (1 := i). rewrite PTree.gcombine; auto.
  rewrite Hi1, Hi2.
  destruct (globdef_linkable_dec fundef_dec V_dec g g0); try (contradict n; auto; fail).
  destruct (globdef_linkable_dec fundef_dec V_dec g0 g); try (contradict n0; auto; fail).
  auto.
Qed.

End LINKER_PROP.
