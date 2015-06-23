Require Import Axioms.
Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_sepcomp.
Require Import Maps Maps_sepcomp.
Require Import Integers Floats Values AST Globalenvs.
Require Import Errors Behaviors Compiler Smallstep.
Require Import Language Linker.
Require Import Tree.
Require Import LinkerBasicproof Sig.
Require Import SepcompRel.

Require SimplExprproof_sepcomp.
Require Selectionproof_sepcomp.
Require Tailcallproof_sepcomp.
Require Inliningproof_sepcomp.
Require Renumberproof_sepcomp.
Require Constpropproof_sepcomp.
Require CSEproof_sepcomp.
Require Deadcodeproof_sepcomp.

Set Implicit Arguments.

(** Lemma on applies *)

Lemma apply_partial_inversion:
  forall A B (a:res A) (f:A -> res B) (b:B),
    (exists a0, a = OK a0 /\ f a0 = OK b) <-> apply_partial _ _ a f = OK b.
Proof.
  constructor; intros.
  - destruct H as [? [? ?]]. subst. auto.
  - destruct a; inv H. eexists. split; eauto.
Qed.

Lemma apply_total_inversion:
  forall A B (a:res A) (f:A -> B) (b:B),
    (exists a0, a = OK a0 /\ f a0 = b) <-> apply_total _ _ a f = OK b.
Proof.
  constructor; intros.
  - destruct H as [? [? ?]]. subst. auto.
  - destruct a; inv H. eexists. split; eauto.
Qed.

Lemma SimplExpr_sepcomp_rel
      cprog clightprog
      (Htrans: SimplExpr.transl_program cprog = OK clightprog):
  @sepcomp_rel
    Language_C Language_Clight
    (fun _ f tf => SimplExprspec.tr_function f tf)
    (fun _ ef tef => ef = tef)
    (@OK _)
    cprog clightprog.
Proof.
  destruct cprog as [defs ?], clightprog as [tdefs ?].
  exploit SimplExprspec.transl_program_spec; eauto. clear Htrans.
  intros [[tglob [Hmatch Htglob]] Hmain]. constructor; auto.
  rewrite app_nil_r in *. simpl in *. subst.
  eapply list_forall2_imply; eauto. intros. inv H1; simpl; split; auto.
  - eexists. split; [reflexivity|].
    inv H2.
    + eapply (@grel_f Language_C Language_Clight); simpl; auto.
    + eapply (@grel_ef Language_C Language_Clight); simpl; auto.
  - eexists. split; [reflexivity|].
    apply (@grel_gv Language_C Language_Clight). auto.
Qed.

Lemma Selection_sepcomp_rel
      cminorprog cminorselprog
      (Htrans: Selection.sel_program cminorprog = OK cminorselprog):
  @sepcomp_rel
    Language_Cminor Language_CminorSel
    (fun p f tf => Selection.sel_function (Genv.globalenv p) f = OK tf)
    (fun p ef tef => ef = tef)
    (@OK _)
    cminorprog cminorselprog.
Proof.
  monadInv Htrans.
  destruct cminorprog as [defs ?], cminorselprog as [tdefs ?].
  unfold transform_partial_program, transform_partial_program2 in EQ0. monadInv EQ0.
  constructor; auto. simpl in *.
  revert tdefs EQ EQ1. generalize defs at 1 2 4 as fdefs.
  induction defs; simpl; intros fdefs tdefs Hhelpers Hdefs.
  { inv Hdefs. constructor. }
  destruct a. destruct g.
  - match goal with
      | [H: match ?x with OK _ => _ | Error _ => _ end = OK _ |- _] =>
        destruct x as [tf|] eqn:Hf; [|inv H]
    end.
    monadInv Hdefs. constructor; simpl.
    + split; auto. eexists. split; [reflexivity|].
      destruct f; inv Hf.
      * monadInv H0.
        eapply (@grel_f Language_Cminor Language_CminorSel); simpl; auto.
      * eapply (@grel_ef Language_Cminor Language_CminorSel); simpl; auto.
    + apply IHdefs; auto.
  - monadInv Hdefs. constructor; simpl.
    + split; auto. eexists. split; [reflexivity|].
      eapply (@grel_gv Language_Cminor Language_CminorSel); auto.
    + apply IHdefs; auto.
Qed.

Lemma Tailcall_sepcomp_rel
      rtlprog1 rtlprog2
      (Htrans: Tailcall.transf_program rtlprog1 = rtlprog2):
  @sepcomp_rel
    Language_RTL Language_RTL
    (fun p f tf => Tailcall.transf_function f = tf)
    (fun p ef tef => ef = tef)
    (@OK _)
    rtlprog1 rtlprog2.
Proof.
  apply transf_program_sepcomp_rel. rewrite <- Htrans.
  unfold Tailcall.transf_program. f_equal.
  apply Axioms.functional_extensionality. intro fd.
  destruct fd; auto.
Qed.

Lemma Inlining_sepcomp_rel
      rtlprog1 rtlprog2
      (Htrans: Inlining.transf_program rtlprog1 = OK rtlprog2):
  @sepcomp_rel
    Language_RTL Language_RTL
    (fun p f tf => Inlining.transf_function (Inlining.funenv_program p) f = OK tf)
    (fun p ef tef => (fun _ ef => OK ef) p ef = OK tef)
    (@OK _)
    rtlprog1 rtlprog2.
Proof.
  apply transf_partial_sepcomp_rel.
  unfold progT, RTL.program, RTL.fundef in *. simpl in *. rewrite <- Htrans.
  unfold Inlining.transf_program. f_equal.
  apply Axioms.functional_extensionality. intro fd.
  destruct fd; auto.
Qed.

Lemma Renumber_sepcomp_rel
      rtlprog1 rtlprog2
      (Htrans: Renumber.transf_program rtlprog1 = rtlprog2):
  @sepcomp_rel
    Language_RTL Language_RTL
    (fun p f tf => Renumber.transf_function f = tf)
    (fun p ef tef => ef = tef)
    (@OK _)
    rtlprog1 rtlprog2.
Proof.
  apply transf_program_sepcomp_rel. rewrite <- Htrans.
  unfold Renumber.transf_program. f_equal.
  apply Axioms.functional_extensionality. intro fd.
  destruct fd; auto.
Qed.

Lemma Constprop_sepcomp_rel
      rtlprog1 rtlprog2
      (Htrans: Constprop.transf_program rtlprog1 = rtlprog2):
  @sepcomp_rel
    Language_RTL Language_RTL
    (fun p f tf => Constprop.transf_function (ValueAnalysis.romem_for_program p) f = tf)
    (fun p ef tef => ef = tef)
    (@OK _)
    rtlprog1 rtlprog2.
Proof.
  apply transf_program_sepcomp_rel. rewrite <- Htrans.
  unfold Constprop.transf_program. f_equal.
  apply Axioms.functional_extensionality. intro fd.
  destruct fd; auto.
Qed.

Lemma CSE_sepcomp_rel
      rtlprog1 rtlprog2
      (Htrans: CSE.transf_program rtlprog1 = OK rtlprog2):
  @sepcomp_rel
    Language_RTL Language_RTL
    (fun p f tf => CSE.transf_function (ValueAnalysis.romem_for_program p) f = OK tf)
    (fun p ef tef => (fun _ ef => OK ef) p ef = OK tef)
    (@OK _)
    rtlprog1 rtlprog2.
Proof.
  apply transf_partial_sepcomp_rel.
  unfold progT, RTL.program, RTL.fundef in *. simpl in *. rewrite <- Htrans.
  unfold CSE.transf_program. f_equal.
  apply Axioms.functional_extensionality. intro fd.
  destruct fd; auto.
Qed.

Lemma Deadcode_sepcomp_rel
      rtlprog1 rtlprog2
      (Htrans: Deadcode.transf_program rtlprog1 = OK rtlprog2):
  @sepcomp_rel
    Language_RTL Language_RTL
    (fun p f tf => Deadcode.transf_function (ValueAnalysis.romem_for_program p) f = OK tf)
    (fun p ef tef => (fun _ ef => OK ef) p ef = OK tef)
    (@OK _)
    rtlprog1 rtlprog2.
Proof.
  apply transf_partial_sepcomp_rel.
  unfold progT, RTL.program, RTL.fundef in *. simpl in *. rewrite <- Htrans.
  unfold Deadcode.transf_program. f_equal.
  apply Axioms.functional_extensionality. intro fd.
  destruct fd; auto.
Qed.

Ltac clarify :=
  repeat (unfold time, print in *;
          try match goal with
                | [TRANSF: Tree.Forall2 (fun _ _ => apply_partial _ _ _ _ = OK _) _ _ |- _] =>
                  eapply Tree.Forall2_compat in TRANSF; [|intros; apply apply_partial_inversion; fail]
                | [TRANSF: Tree.Forall2 (fun _ _ => apply_total _ _ _ _ = OK _) _ _ |- _] =>
                  eapply Tree.Forall2_compat in TRANSF; [|intros; apply apply_total_inversion; fail]
                | [TRANSF: Tree.Forall2 (fun a b => OK a = OK b) _ _ |- _] =>
                  eapply Tree.Forall2_compat in TRANSF; [|instantiate (1 := eq); constructor; intro X; inv X; auto; fail]
                | [TRANSF: Tree.Forall2 (fun a b => a = b) _ _ |- _] =>
                  eapply Tree.Forall2_compat in TRANSF; [|instantiate (1 := eq); constructor; intro X; inv X; auto; fail]
                | [TRANSF: Tree.Forall2 (fun _ _ => exists _, _ /\ _) _ _ |- _] =>
                  let p := fresh "p" in
                  let T := fresh "T" in
                  apply Tree.Forall2_split in TRANSF; destruct TRANSF as [p [T TRANSF]]
                | [TRANSF: Tree.Forall2 eq _ _ |- _] =>
                  apply Tree.Forall2_eq in TRANSF; subst
              end).

Ltac simplify :=
  intros; subst;
  repeat match goal with
           | [H: OK _ = OK _ |- _] => inv H
           | [H: bind _ _ = OK _ |- _] => monadInv H
           | [H: _ /\ _ |- _] => destruct H
         end;
  subst; auto.

Theorem linker_correct_det_forward
        ctree asmtree cprog
        (CLINK: Tree.reduce (link_program Language_C) ctree = Some cprog)
        (TRANSF: Tree.Forall2 (fun c a => transf_c_program c = OK a) ctree asmtree):
  exists (asmprog:Asm.program)
    (_:forward_simulation (Cstrategy.semantics cprog) (Asm.semantics asmprog)),
    Tree.reduce (link_program Language_Asm) asmtree = Some asmprog.
Proof.
  repeat intro.

  (* C *)
  unfold transf_c_program in TRANSF. clarify.

  eapply Tree.Forall2_implies in T; [|apply SimplExpr_sepcomp_rel].
  eapply Tree.Forall2_reduce in T; eauto;
    [|eapply (@link_program_sepcomp_rel Language_C Language_Clight id)]; simplify;
    [|apply SimplExpr_sig; auto].
  destruct T as [clightprog [Hclightprog Hclightsim]].
  apply SimplExprproof_sepcomp.transl_program_correct in Hclightsim.

  (* Clight *)
  unfold transf_clight_program in TRANSF. clarify.

  eapply Tree.Forall2_reduce in T1; eauto;
    [|eapply (transform_partial_program2_link_program Language_Clight Language_Clight)];
    [|apply SimplLocals_sig].
  destruct T1 as [clight2prog [Hclight2prog Hclight2sim]].
  apply SimplLocalsproof.transf_program_correct in Hclight2sim.

  eapply Tree.Forall2_reduce in T0; eauto;
    [|eapply (transform_partial_program2_link_program Language_Clight Language_Csharpminor)];
    [|apply Cshmgen_sig].
  destruct T0 as [csharpminorprog [Hsharpminorprog Hsharpminorsim]].
  apply Cshmgenproof.transl_program_correct in Hsharpminorsim.

  eapply Tree.Forall2_reduce in T; eauto;
    [|eapply (transform_partial_program2_link_program Language_Csharpminor Language_Cminor)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply Cminorgen_sig].
  destruct T as [cminorprog [Hcminorprog Hcminorsim]].
  apply Cminorgenproof.transl_program_correct in Hcminorsim.

  (* Cminor *)
  unfold transf_cminor_program in TRANSF. clarify.

  assert (Hcheck_helpers: SelectLong.check_helpers (Genv.globalenv cminorprog) = OK tt).
  {
    exploit Tree.Forall_reduce; [| |eauto|].
    - eapply Selectionproof_sepcomp.link_program_check_helpers.
    - clear -T0. revert p5 T0.
      induction p6; intros; inv T0; econstructor; eauto.
      monadInv Hpred. destruct x. auto.
    - auto.
  }

  eapply Tree.Forall2_implies in T0; [|apply Selection_sepcomp_rel].
  eapply Tree.Forall2_reduce in T0; eauto;
    [|eapply (@link_program_sepcomp_rel Language_Cminor Language_CminorSel id)]; simplify;
    [|eapply Selection_sig; eauto].

  destruct T0 as [cminorselprog [Hcminorselprog Hcminorselsim]].
  apply Selectionproof_sepcomp.transl_program_correct in Hcminorselsim;
    eauto using Selectionproof.check_helpers_correct.

  eapply Tree.Forall2_reduce in T; eauto;
    [|eapply (transform_partial_program2_link_program Language_CminorSel Language_RTL)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply RTLgen_sig].
  destruct T as [rtlprog0 [Hrtlprog0 Hrtlsim0]].
  apply RTLgenproof.transf_program_correct in Hrtlsim0.

  (* RTL *)
  unfold transf_rtl_program in TRANSF. clarify.

  eapply Tree.Forall2_implies in T19; [|apply Tailcall_sepcomp_rel].
  eapply Tree.Forall2_reduce in T19; eauto; [|eapply (@link_program_sepcomp_rel Language_RTL Language_RTL id)]; simplify;
    [|apply Tailcall_sig].
  destruct T19 as [rtlprog1 [Hrtlprog1 Hrtlsim1]].
  apply Tailcallproof_sepcomp.transf_program_correct in Hrtlsim1.

  eapply Tree.Forall2_implies in T17; [|apply Inlining_sepcomp_rel].
  eapply Tree.Forall2_reduce in T17; eauto; [|eapply (@link_program_sepcomp_rel Language_RTL Language_RTL id)]; simplify;
    [|eapply Inlining_sig; eauto].
  destruct T17 as [rtlprog2 [Hrtlprog2 Hrtlsim2]].
  apply Inliningproof_sepcomp.transf_program_correct in Hrtlsim2.

  eapply Tree.Forall2_implies in T15; [|apply Renumber_sepcomp_rel].
  eapply Tree.Forall2_reduce in T15; eauto; [|eapply (@link_program_sepcomp_rel Language_RTL Language_RTL id)]; simplify.
  destruct T15 as [rtlprog3 [Hrtlprog3 Hrtlsim3]].
  apply Renumberproof_sepcomp.transf_program_correct in Hrtlsim3.

  eapply Tree.Forall2_implies in T13; [|apply Constprop_sepcomp_rel].
  eapply Tree.Forall2_reduce in T13; eauto; [|eapply (@link_program_sepcomp_rel Language_RTL Language_RTL id)]; simplify.
  destruct T13 as [rtlprog4 [Hrtlprog4 Hrtlsim4]].
  apply Constpropproof_sepcomp.transf_program_correct in Hrtlsim4.

  eapply Tree.Forall2_implies in T11; [|apply Renumber_sepcomp_rel].
  eapply Tree.Forall2_reduce in T11; eauto; [|eapply (@link_program_sepcomp_rel Language_RTL Language_RTL id)]; simplify.
  destruct T11 as [rtlprog5 [Hrtlprog5 Hrtlsim5]].
  apply Renumberproof_sepcomp.transf_program_correct in Hrtlsim5.

  eapply Tree.Forall2_implies in T9; [|apply CSE_sepcomp_rel].
  eapply Tree.Forall2_reduce in T9; eauto; [|eapply (@link_program_sepcomp_rel Language_RTL Language_RTL id)]; simplify;
    [|eapply CSE_sig; eauto].
  destruct T9 as [rtlprog6 [Hrtlprog6 Hrtlsim6]].
  apply CSEproof_sepcomp.transf_program_correct in Hrtlsim6.

  eapply Tree.Forall2_implies in T7; [|apply Deadcode_sepcomp_rel].
  eapply Tree.Forall2_reduce in T7; eauto; [|eapply (@link_program_sepcomp_rel Language_RTL Language_RTL id)]; simplify;
    [|eapply Deadcode_sig; eauto].
  destruct T7 as [rtlprog7 [Hrtlprog7 Hrtlsim7]].
  apply Deadcodeproof_sepcomp.transf_program_correct in Hrtlsim7.

  eapply Tree.Forall2_reduce in T5; eauto;
    [|eapply (transform_partial_program2_link_program Language_RTL Language_LTL)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply Allocation_sig].
  destruct T5 as [ltlprog0 [Hltlprog0 Hltlsim0]].
  apply Allocproof.transf_program_correct in Hltlsim0.

  eapply Tree.Forall2_reduce in T3; eauto;
    [|eapply (transform_program_link_program); auto].
  destruct T3 as [ltlprog1 [Hltlprog1 Hltlsim1]]. subst.
  generalize (Tunnelingproof.transf_program_correct ltlprog0) as Hltlsim1. intro.

  eapply Tree.Forall2_reduce in T2; eauto;
    [|eapply (transform_partial_program2_link_program Language_LTL Language_Linear)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply Linearize_sig].
  destruct T2 as [linearprog0 [Hlinearprog0 Hlinearsim0]].
  apply Linearizeproof.transf_program_correct in Hlinearsim0.

  eapply Tree.Forall2_reduce in T1; eauto;
    [|eapply (transform_program_link_program); auto].
  destruct T1 as [linearprog1 [Hlinearprog1 Hlinearsim1]]. subst.
  generalize (CleanupLabelsproof.transf_program_correct linearprog0) as Hlinearsim1. intro.

  eapply Tree.Forall2_reduce in T0; eauto;
    [|eapply (transform_partial_program2_link_program Language_Linear Language_Mach)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply Stacking_sig].
  destruct T0 as [machprog [Hmachprog Hmachsim]].
  eapply Stackingproof.transf_program_correct in Hmachsim; eauto;
    [|eexact Asmgenproof.return_address_exists; eassumption].

  eapply Tree.Forall2_reduce in TRANSF; eauto;
    [|eapply (transform_partial_program2_link_program Language_Mach Language_Asm)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply Asmgen_sig].
  destruct TRANSF as [asmprog [Hasmprog Hasmsim]].
  eapply Asmgenproof.transf_program_correct in Hasmsim; eauto.

  (* epilogue *)
  exists asmprog. eexists; auto.
  repeat (auto; try (eapply compose_forward_simulation; [|eauto; fail])).
Qed.

Theorem linker_correct_det_backward
        ctree asmtree cprog
        (CLINK: Tree.reduce (link_program Language_C) ctree = Some cprog)
        (TRANSF: Tree.Forall2 (fun c a => transf_c_program c = OK a) ctree asmtree):
  exists (asmprog:Asm.program)
    (_:backward_simulation (atomic (Cstrategy.semantics cprog)) (Asm.semantics asmprog)),
    Tree.reduce (link_program Language_Asm) asmtree = Some asmprog.
Proof.
  exploit linker_correct_det_forward; eauto.
  intros. destruct H as [asmprog [fsim Hasm]].
  exists asmprog.
  eexists; auto.
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces. eapply Asm.semantics_determinate.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem linker_correct
        ctree asmtree cprog
        (CLINK: Tree.reduce (link_program Language_C) ctree = Some cprog)
        (TRANSF: Tree.Forall2 (fun c a => transf_c_program c = OK a) ctree asmtree):
  exists (asmprog:Asm.program)
    (_:backward_simulation (Csem.semantics cprog) (Asm.semantics asmprog)),
    Tree.reduce (link_program Language_Asm) asmtree = Some asmprog.
Proof.
  exploit linker_correct_det_backward; eauto.
  intros. destruct H as [asmprog [fsim Hasm]].
  exists asmprog.
  eexists; eauto.
  apply compose_backward_simulation with (atomic (Cstrategy.semantics cprog)).
  eapply sd_traces; eapply Asm.semantics_determinate.
  apply factor_backward_simulation. 
  apply Cstrategy.strategy_simulation.
  apply Csem.semantics_single_events.
  eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  exact fsim.
Qed.
