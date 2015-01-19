Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_sepcomp.
Require Import Maps Maps_sepcomp.
Require Import Integers Floats Values AST Globalenvs.
Require Import Errors Behaviors Compiler Smallstep.
Require Import Language Linker.

Set Implicit Arguments.

Lemma OK_eq_inversion A (a b:A):
  OK a = OK b -> a = b.
Proof. intro. inv H. auto. Qed.

Ltac clarify :=
  repeat match goal with
           | [H: context[if ?b then _ else _]|- _] =>
             let X := fresh "X" in destruct b eqn:X
           | [H: context[match ?b with OK _ => _ | Error _ => _ end]|- _] =>
             let X := fresh "X" in destruct b
           | [H: context[match ?b with Some _ => _ | None => _ end]|- _] =>
             let X := fresh "X" in destruct b
           | [H: bind _ _ = OK _ |- _] => monadInv H
           | [H: OK _ = OK _ |- _] => apply OK_eq_inversion in H; subst
           | [H: OK _ = Error _ |- _] => inv H
           | [H: Error _ = OK _ |- _] => inv H
           | [H: Some _ = Some _ |- _] => inv H
           | [H: Some _ = None _ |- _] => inv H
           | [H: None = Some _ |- _] => inv H
           | [H: inl _ = inl _ |- _] => inv H
           | [H: inl _ = inr _ |- _] => inv H
           | [H: inr _ = inl _ |- _] => inv H
           | [H: inr _ = inr _ |- _] => inv H
         end.

Lemma Asmgen_sig:
  forall (f1 : F_Mach) (f2 : F_Asm),
    Asmgen.transf_function f1 = OK f2 -> F_sig F_Mach f1 = F_sig F_Asm f2.
Proof.
  intros.
  unfold Asmgen.transf_function in H. monadInv H.
  unfold Asmgen.transl_function in EQ. monadInv EQ.
  clarify. auto.
Qed.

Lemma Stacking_sig:
  forall (f1 : F_Linear) (f2 : F_Mach),
    Stacking.transf_function f1 = OK f2 -> F_sig F_Linear f1 = F_sig F_Mach f2.
Proof.
  intros. unfold Stacking.transf_function in H. clarify. auto.
Qed.

Lemma Linearize_sig:
  forall (f1 : F_LTL) (f2 : F_Linear),
    Linearize.transf_function f1 = OK f2 -> F_sig F_LTL f1 = F_sig F_Linear f2.
Proof.
  intros. unfold Linearize.transf_function in H. monadInv H. auto.
Qed.

Lemma Allocation_sig:
  forall (f1 : F_RTL) (f2 : F_LTL),
    Allocation.transf_function f1 = OK f2 -> F_sig F_RTL f1 = F_sig F_LTL f2.
Proof.
  intros.
  unfold Allocation.transf_function in H. clarify.
  unfold Allocation.check_function in EQ. clarify.
  monadInv EQ. clarify.
  unfold Allocation.transfer in EQ0. clarify.
  unfold Allocation.check_entrypoints_aux in X. clarify. auto.
Qed.

Lemma RTLgen_sig:
  forall (f1 : F_CminorSel) (f2 : F_RTL),
    RTLgen.transl_function f1 = OK f2 -> F_sig F_CminorSel f1 = F_sig F_RTL f2.
Proof.
  intros. unfold RTLgen.transl_function in H. clarify.
  destruct (RTLgen.reserve_labels (CminorSel.fn_body f1) (PTree.empty RTL.node, RTLgen.init_state)).
  destruct (RTLgen.transl_fun f1 l s); inv H.
  destruct p. inv H1. auto.
Qed.

Lemma Cminorgen_sig:
  forall (f1 : F_Csharpminor) (f2 : F_Cminor),
    Cminorgen.transl_function f1 = OK f2 -> F_sig F_Csharpminor f1 = F_sig F_Cminor f2.
Proof.
  intros. unfold Cminorgen.transl_function in H.
  destruct (Cminorgen.build_compilenv f1). clarify.
  unfold Cminorgen.transl_funbody in H. monadInv H. auto.
Qed.

Lemma Cshmgen_sig:
  forall (f1 f2 : fundefT Language_Clight)
         (f1' f2' : fundefT Language_Csharpminor),
    globfun_linkable Language_Clight f1 f2 ->
    Cshmgen.transl_fundef f1 = OK f1' ->
    Cshmgen.transl_fundef f2 = OK f2' ->
    globfun_linkable Language_Csharpminor f1' f2'.
Proof.
  simpl. intros.
  destruct f1, f2; simpl in *; clarify;
    inv H; simpl in *; clarify.
  - inv Hsig. eapply globfun_linkable_ei; simpl; eauto. rewrite e0.
    unfold Cshmgen.transl_function in EQ. clarify. simpl.
    unfold Ctypes.signature_of_type, Cshmgen.signature_of_function.
    f_equal. symmetry. apply Cshmgenproof.transl_params_types.
  - eapply globfun_linkable_ee; simpl; auto.
Qed.

Lemma SimplLocals_sig:
  forall f1 f2 f1' f2' : fundefT Language_Clight,
    globfun_linkable Language_Clight f1 f2 ->
    SimplLocals.transf_fundef f1 = OK f1' ->
    SimplLocals.transf_fundef f2 = OK f2' ->
    globfun_linkable Language_Clight f1' f2'.
Proof.
  simpl. intros.
  destruct f1, f2; simpl in *; clarify;
    inv H; simpl in *; clarify.
  - inv Hsig. eapply globfun_linkable_ei; simpl; eauto.
    unfold SimplLocals.transf_function in EQ. clarify; auto.
    inv EQ.
  - eapply globfun_linkable_ee; simpl; auto.
Qed.

Lemma globfun_linkable_transf_partial_fundef
      (fT1 fT2:F Sig_signature) vT
      tf (Htf: forall (f1:fT1) (f2:fT2) (Hf: tf f1 = OK f2), fT1.(F_sig) f1 = fT2.(F_sig) f2)
      (f1 f2:(mkLanguage (Fundef_common fT1) vT).(fundefT)) (f1' f2':(mkLanguage (Fundef_common fT2) vT).(fundefT))
      (Hlink: globfun_linkable (mkLanguage (Fundef_common fT1) vT) f1 f2)
      (H1: transf_partial_fundef tf f1 = OK f1')
      (H2: transf_partial_fundef tf f2 = OK f2'):
  globfun_linkable (mkLanguage (Fundef_common fT2) vT) f1' f2'.
Proof.
  simpl in *.
  destruct f1, f2; inv H1; inv H2; inv Hlink; simpl in *; clarify.
  - destruct (tf i2) eqn:Hi2; inv EQ.
    eapply globfun_linkable_ei; simpl; eauto.
    rewrite Hsig. erewrite Htf; eauto.
  - eapply globfun_linkable_ee; simpl; eauto.
Qed.
