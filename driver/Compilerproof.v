(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** The whole compiler and its proof of semantic preservation *)

(** Libraries. *)
Require Import String.
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Smallstep.
(** Languages (syntax and semantics). *)
Require Csyntax.
Require Csem.
Require Cstrategy.
Require Cexec.
Require Clight.
Require Csharpminor.
Require Cminor.
Require CminorSel.
Require RTL.
Require LTL.
Require Linear.
Require Mach.
Require Asm.
(** Translation passes. *)
Require Initializers.
Require SimplExpr.
Require SimplLocals.
Require Cshmgen.
Require Cminorgen.
Require Selection.
Require RTLgen.
Require Tailcall.
Require Inlining.
Require Renumber.
Require Constprop.
Require CSE.
Require Deadcode.
Require Allocation.
Require Tunneling.
Require Linearize.
Require CleanupLabels.
Require Stacking.
Require Asmgen.
(** Proofs of semantic preservation. *)
Require SimplExprproof.
Require SimplLocalsproof.
Require Cshmgenproof.
Require Cminorgenproof.
Require Selectionproof.
Require RTLgenproof.
Require Tailcallproof.
Require Inliningproof.
Require Renumberproof.
Require Constpropproof.
Require CSEproof.
Require Deadcodeproof.
Require Allocproof.
Require Tunnelingproof.
Require Linearizeproof.
Require CleanupLabelsproof.
Require Stackingproof.
Require Asmgenproof.
(** Command-line flags. *)
Require Import Compopts.

Require Import Compiler.
Require Import Linkerproof.

(** * Semantic preservation *)

(** We prove that the [transf_program] translations preserve semantics
  by constructing the following simulations:
- Forward simulations from [Cstrategy] / [Cminor] / [RTL] to [Asm]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Asm]).
- Backward simulation from [Csem] to [Asm]
  (composition of two backward simulations).

These results establish the correctness of the whole compiler! *)

Theorem transf_rtl_program_correct:
  forall p tp,
  transf_rtl_program p = OK tp ->
  forward_simulation (RTL.semantics p) (Asm.semantics tp)
  * backward_simulation (RTL.semantics p) (Asm.semantics tp).
Proof.
  intros.
  assert (F: forward_simulation (RTL.semantics p) (Asm.semantics tp)).
  unfold transf_rtl_program, time in H.
  repeat rewrite compose_print_identity in H.
  simpl in H.
  set (p1 := total_if optim_tailcalls Tailcall.transf_program p) in *.
  destruct (Inlining.transf_program p1) as [p11|] eqn:?; simpl in H; try discriminate.
  set (p12 := Renumber.transf_program p11) in *.
  set (p2 := total_if optim_constprop Constprop.transf_program p12) in *.
  set (p21 := total_if optim_constprop Renumber.transf_program p2) in *.
  destruct (partial_if optim_CSE CSE.transf_program p21) as [p3|] eqn:?; simpl in H; try discriminate.
  destruct (partial_if optim_redundancy Deadcode.transf_program p3) as [p31|] eqn:?; simpl in H; try discriminate.
  destruct (Allocation.transf_program p31) as [p4|] eqn:?; simpl in H; try discriminate.
  set (p5 := Tunneling.tunnel_program p4) in *.
  destruct (Linearize.transf_program p5) as [p6|] eqn:?; simpl in H; try discriminate.
  set (p7 := CleanupLabels.transf_program p6) in *.
  destruct (Stacking.transf_program p7) as [p8|] eqn:?; simpl in H; try discriminate.
  apply compose_forward_simulation with (RTL.semantics p1).
    apply total_if_simulation. intros. apply Tailcallproof.transf_program_correct. apply Tailcallproof.Tailcall_sepcomp_rel. auto. 
  apply compose_forward_simulation with (RTL.semantics p11).
    apply Inliningproof.transf_program_correct; auto. apply Inliningproof.Inlining_sepcomp_rel. auto.
  apply compose_forward_simulation with (RTL.semantics p12).
    apply Renumberproof.transf_program_correct. apply Renumberproof.Renumber_sepcomp_rel. auto. 
  apply compose_forward_simulation with (RTL.semantics p2).
    apply total_if_simulation. intros. apply Constpropproof.transf_program_correct. apply Constpropproof.Constprop_sepcomp_rel. auto.
  apply compose_forward_simulation with (RTL.semantics p21).
    apply total_if_simulation. intros. apply Renumberproof.transf_program_correct. apply Renumberproof.Renumber_sepcomp_rel. auto. 
  apply compose_forward_simulation with (RTL.semantics p3).
    eapply partial_if_simulation; eauto. intros. apply CSEproof.transf_program_correct. apply CSEproof.CSE_sepcomp_rel. auto.
  apply compose_forward_simulation with (RTL.semantics p31).
    eapply partial_if_simulation; eauto. intros. apply Deadcodeproof.transf_program_correct. apply Deadcodeproof.Deadcode_sepcomp_rel. auto.
  apply compose_forward_simulation with (LTL.semantics p4).
    apply Allocproof.transf_program_correct; auto.
  apply compose_forward_simulation with (LTL.semantics p5).
    apply Tunnelingproof.transf_program_correct.
  apply compose_forward_simulation with (Linear.semantics p6).
    apply Linearizeproof.transf_program_correct; auto.
  apply compose_forward_simulation with (Linear.semantics p7).
    apply CleanupLabelsproof.transf_program_correct. 
  apply compose_forward_simulation with (Mach.semantics Asmgenproof0.return_address_offset p8).
    apply Stackingproof.transf_program_correct.
    exact Asmgenproof.return_address_exists.
    auto.
  apply Asmgenproof.transf_program_correct; eauto.
  split. auto. 
  apply forward_to_backward_simulation. auto. 
  apply RTL.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem transf_cminor_program_correct:
  forall p tp,
  transf_cminor_program p = OK tp ->
  forward_simulation (Cminor.semantics p) (Asm.semantics tp)
  * backward_simulation (Cminor.semantics p) (Asm.semantics tp).
Proof.
  intros.
  assert (F: forward_simulation (Cminor.semantics p) (Asm.semantics tp)).
  unfold transf_cminor_program, time in H.
  repeat rewrite compose_print_identity in H.
  simpl in H. 
  destruct (Selection.sel_program p) as [p1|] eqn:?; simpl in H; try discriminate.
  destruct (RTLgen.transl_program p1) as [p2|] eqn:?; simpl in H; try discriminate.
  eapply compose_forward_simulation. apply Selectionproof.transl_program_correct. monadInv Heqr. eapply Selectionproof.check_helpers_correct. eauto. apply Selectionproof.Selection_sepcomp_rel. eauto.
  eapply compose_forward_simulation. apply RTLgenproof.transf_program_correct. eassumption.
  exact (fst (transf_rtl_program_correct _ _ H)).

  split. auto. 
  apply forward_to_backward_simulation. auto. 
  apply Cminor.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem transf_clight_program_correct:
  forall p tp,
  transf_clight_program p = OK tp ->
  forward_simulation (Clight.semantics1 p) (Asm.semantics tp)
  * backward_simulation (Clight.semantics1 p) (Asm.semantics tp).
Proof.
  intros. 
  assert (F: forward_simulation (Clight.semantics1 p) (Asm.semantics tp)).
  revert H; unfold transf_clight_program, time; simpl.
  rewrite print_identity.
  caseEq (SimplLocals.transf_program p); simpl; try congruence; intros p0 EQ0.
  caseEq (Cshmgen.transl_program p0); simpl; try congruence; intros p1 EQ1.
  caseEq (Cminorgen.transl_program p1); simpl; try congruence; intros p2 EQ2.
  intros EQ3.
  eapply compose_forward_simulation. apply SimplLocalsproof.transf_program_correct. eauto.
  eapply compose_forward_simulation. apply Cshmgenproof.transl_program_correct. eauto.
  eapply compose_forward_simulation. apply Cminorgenproof.transl_program_correct. eauto.
  exact (fst (transf_cminor_program_correct _ _ EQ3)). 

  split. auto. 
  apply forward_to_backward_simulation. auto. 
  apply Clight.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem transf_cstrategy_program_correct:
  forall p tp,
  transf_c_program p = OK tp ->
  forward_simulation (Cstrategy.semantics p) (Asm.semantics tp)
  * backward_simulation (atomic (Cstrategy.semantics p)) (Asm.semantics tp).
Proof.
  intros.
  assert (F: forward_simulation (Cstrategy.semantics p) (Asm.semantics tp)).
  revert H; unfold transf_c_program, time; simpl.
  caseEq (SimplExpr.transl_program p); simpl; try congruence; intros p0 EQ0.
  intros EQ1.
  eapply compose_forward_simulation. apply SimplExprproof.transl_program_correct. apply SimplExprproof.SimplExpr_sepcomp_rel. eauto.
  exact (fst (transf_clight_program_correct _ _ EQ1)). 

  split. auto. 
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces. eapply Asm.semantics_determinate.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem transf_c_program_correct:
  forall p tp,
  transf_c_program p = OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  intros. 
  apply compose_backward_simulation with (atomic (Cstrategy.semantics p)).
  eapply sd_traces; eapply Asm.semantics_determinate.
  apply factor_backward_simulation. 
  apply Cstrategy.strategy_simulation.
  apply Csem.semantics_single_events.
  eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  exact (snd (transf_cstrategy_program_correct _ _ H)).
Qed.
