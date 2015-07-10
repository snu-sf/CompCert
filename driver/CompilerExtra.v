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

Require Import Compiler.
(** Command-line flags. *)
Require Import Compopts.

Open Local Scope string_scope.

Inductive rtl_pass: Type :=
| Tailcall: rtl_pass
| Inlining: rtl_pass
| Renumber: rtl_pass
| Constprop: rtl_pass
| CSE: rtl_pass
| Deadcode: rtl_pass.

Definition opt_list:= list (rtl_pass * (unit -> bool)).
Definition tflag := (fun (t:unit) => true).
Definition fflag := (fun (t:unit) => false).

Definition transf_rtl_program_to_asm_opt (p: res RTL.program) : res Asm.program :=
   p
   @@ print (print_RTL 7)
  @@@ time "Register allocation" Allocation.transf_program
   @@ print print_LTL
   @@ time "Branch tunneling" Tunneling.tunnel_program
  @@@ time "CFG linearization" Linearize.transf_program
   @@ time "Label cleanup" CleanupLabels.transf_program
  @@@ time "Mach generation" Stacking.transf_program
   @@ print print_Mach
  @@@ time "Asm generation" Asmgen.transf_program.


Fixpoint transf_rtl_program_opt' (z:Z) (l:opt_list) (p: res RTL.program) : res Asm.program :=
  match l with
    | nil =>
      transf_rtl_program_to_asm_opt p
    | (pass, flag)::l' =>
      let p' := p @@ print (print_RTL z) in
      let p'' :=
          match pass with
            | Tailcall => p' @@ total_if flag (time "Tail calls" Tailcall.transf_program)
            | Inlining => p' @@@ partial_if flag (time "Inlining" Inlining.transf_program)
            | Renumber => p' @@ total_if flag (time "Renumbering" Renumber.transf_program)
            | Constprop => p' @@ total_if flag (time "Constant propagation" Constprop.transf_program)
            | CSE => p' @@@ partial_if flag (time "CSE" CSE.transf_program)
            | Deadcode => p' @@@ partial_if flag (time "Redundancy elimination" Deadcode.transf_program)
          end
      in transf_rtl_program_opt' (z+1) l' p''
  end.

Definition transf_rtl_program_opt (z:Z) (l:opt_list) (p: RTL.program) : res Asm.program :=
  transf_rtl_program_opt' z l (OK p).
  
Definition transf_cminor_program_opt (l:opt_list) (p: Cminor.program) : res Asm.program :=
  OK p
  @@ print print_Cminor
  @@@ time "Instruction selection" Selection.sel_program
  @@@ time "RTL generation" RTLgen.transl_program
  @@@ transf_rtl_program_opt 0 l.

Definition transf_clight_program_opt (l: opt_list) (p: Clight.program) : res Asm.program :=
  OK p
  @@ print print_Clight
  @@@ time "Simplification of locals" SimplLocals.transf_program
  @@@ time "C#minor generation" Cshmgen.transl_program
  @@@ time "Cminor generation" Cminorgen.transl_program
  @@@ transf_cminor_program_opt l.

Definition transf_c_program_opt l p : res Asm.program :=
  OK p
     @@@ time "Clight generation" SimplExpr.transl_program
     @@@ transf_clight_program_opt l.

Definition compiler_flag :=
    (Tailcall, optim_tailcalls)::(Inlining, tflag)::(Renumber, tflag)::(Constprop, optim_constprop)
  ::(Renumber, optim_constprop)::(CSE, optim_CSE)::(Deadcode, optim_redundancy)::nil.

Require Import FunctionalExtensionality.

Theorem compiler_equivalence:
  transf_c_program = transf_c_program_opt compiler_flag.
Proof. reflexivity. Qed.


Lemma transf_rtl_program_opt'_error: forall l n msg, transf_rtl_program_opt' n l (Error msg) = Error msg.
Proof.
  intros l. induction l; intros; eauto.
  simpl. destruct a. destruct r; eauto.
Qed.

Theorem transf_rtl_program_opt_correct:
  forall n l p tp,
  transf_rtl_program_opt n l p = OK tp ->
  forward_simulation (RTL.semantics p) (Asm.semantics tp)
  * backward_simulation (RTL.semantics p) (Asm.semantics tp).
Proof.
  intros.
  assert (F: forward_simulation (RTL.semantics p) (Asm.semantics tp)).
  { generalize dependent p. generalize dependent n. generalize dependent tp.
    induction l; intros.
    - unfold transf_rtl_program_opt in H.
      simpl in H.
      unfold transf_rtl_program_to_asm_opt, time in H.
      repeat rewrite compose_print_identity in H.
      simpl in H.
      destruct (Allocation.transf_program p) as [p4|] eqn:?; simpl in H; try discriminate.
      set (p5 := Tunneling.tunnel_program p4) in *.
      destruct (Linearize.transf_program p5) as [p6|] eqn:?; simpl in H; try discriminate.
      set (p7 := CleanupLabels.transf_program p6) in *.
      destruct (Stacking.transf_program p7) as [p8|] eqn:?; simpl in H; try discriminate.

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
    - unfold transf_rtl_program_opt in H.
      simpl in H.
      destruct a as [pass flag].
      destruct pass; unfold print, time in H.
      + set (p1 := total_if flag Tailcall.transf_program p).
        apply compose_forward_simulation with (RTL.semantics p1); eauto.
        apply total_if_simulation. intros. apply Tailcallproof.transf_program_correct.
        apply Tailcallproof.Tailcall_sepcomp_rel. auto.
      + set (p1' := partial_if flag Inlining.transf_program p).
        destruct p1' as [p1|] eqn:Hp1; [| subst; rewrite Hp1 in H; rewrite transf_rtl_program_opt'_error in H; inv H].
        apply compose_forward_simulation with (RTL.semantics p1);
          [|eapply IHl; unfold transf_rtl_program_opt; subst; rewrite <- Hp1; eauto].
        subst.
        eapply partial_if_simulation; eauto. intros.
        apply Inliningproof.transf_program_correct; auto. apply Inliningproof.Inlining_sepcomp_rel. auto.
      + set (p1 := total_if flag Renumber.transf_program p).
        apply compose_forward_simulation with (RTL.semantics p1); eauto.
        apply total_if_simulation. intros. apply Renumberproof.transf_program_correct.
        apply Renumberproof.Renumber_sepcomp_rel. auto.
      + set (p1 := total_if flag Constprop.transf_program p).
        apply compose_forward_simulation with (RTL.semantics p1); eauto.
        apply total_if_simulation. intros. apply Constpropproof.transf_program_correct.
        apply Constpropproof.Constprop_sepcomp_rel. auto.
      + set (p1' := partial_if flag CSE.transf_program p).
        destruct p1' as [p1|] eqn:Hp1; [| subst; rewrite Hp1 in H; rewrite transf_rtl_program_opt'_error in H; inv H].
        apply compose_forward_simulation with (RTL.semantics p1);
          [|eapply IHl; unfold transf_rtl_program_opt; subst; rewrite <- Hp1; eauto].
        subst.
        eapply partial_if_simulation; eauto. intros.
        apply CSEproof.transf_program_correct; auto. apply CSEproof.CSE_sepcomp_rel. auto.
      + set (p1' := partial_if flag Deadcode.transf_program p).
        destruct p1' as [p1|] eqn:Hp1; [| subst; rewrite Hp1 in H; rewrite transf_rtl_program_opt'_error in H; inv H].
        apply compose_forward_simulation with (RTL.semantics p1);
          [|eapply IHl; unfold transf_rtl_program_opt; subst; rewrite <- Hp1; eauto].
        subst.
        eapply partial_if_simulation; eauto. intros.
        apply Deadcodeproof.transf_program_correct; auto. apply Deadcodeproof.Deadcode_sepcomp_rel. auto.
  }
  split. auto. 
  apply forward_to_backward_simulation. auto. 
  apply RTL.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem transf_cminor_program_opt_correct:
  forall l p tp,
  transf_cminor_program_opt l p = OK tp ->
  forward_simulation (Cminor.semantics p) (Asm.semantics tp)
  * backward_simulation (Cminor.semantics p) (Asm.semantics tp).
Proof.
  intros.
  assert (F: forward_simulation (Cminor.semantics p) (Asm.semantics tp)).
  unfold transf_cminor_program_opt, time in H.
  repeat rewrite compose_print_identity in H.
  simpl in H. 
  destruct (Selection.sel_program p) as [p1|] eqn:?; simpl in H; try discriminate.
  destruct (RTLgen.transl_program p1) as [p2|] eqn:?; simpl in H; try discriminate.
  eapply compose_forward_simulation. apply Selectionproof.transf_program_correct. monadInv Heqr. destruct x; apply EQ. apply Selectionproof.Selection_sepcomp_rel. eauto.
  eapply compose_forward_simulation. apply RTLgenproof.transf_program_correct. eassumption.
  exact (fst (transf_rtl_program_opt_correct _ _ _ _ H)).

  split. auto. 
  apply forward_to_backward_simulation. auto. 
  apply Cminor.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem transf_clight_program_opt_correct:
  forall l p tp,
  transf_clight_program_opt l p = OK tp ->
  forward_simulation (Clight.semantics1 p) (Asm.semantics tp)
  * backward_simulation (Clight.semantics1 p) (Asm.semantics tp).
Proof.
  intros. 
  assert (F: forward_simulation (Clight.semantics1 p) (Asm.semantics tp)).
  revert H; unfold transf_clight_program_opt, time; simpl.
  rewrite print_identity.
  caseEq (SimplLocals.transf_program p); simpl; try congruence; intros p0 EQ0.
  caseEq (Cshmgen.transl_program p0); simpl; try congruence; intros p1 EQ1.
  caseEq (Cminorgen.transl_program p1); simpl; try congruence; intros p2 EQ2.
  intros EQ3.
  eapply compose_forward_simulation. apply SimplLocalsproof.transf_program_correct. eauto.
  eapply compose_forward_simulation. apply Cshmgenproof.transl_program_correct. eauto.
  eapply compose_forward_simulation. apply Cminorgenproof.transl_program_correct. eauto.
  exact (fst (transf_cminor_program_opt_correct _ _ _ EQ3)). 

  split. auto. 
  apply forward_to_backward_simulation. auto. 
  apply Clight.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem transf_cstrategy_program_opt_correct:
  forall l p tp,
  transf_c_program_opt l p = OK tp ->
  forward_simulation (Cstrategy.semantics p) (Asm.semantics tp)
  * backward_simulation (atomic (Cstrategy.semantics p)) (Asm.semantics tp).
Proof.
  intros.
  assert (F: forward_simulation (Cstrategy.semantics p) (Asm.semantics tp)).
  revert H; unfold transf_c_program_opt, time; simpl.
  caseEq (SimplExpr.transl_program p); simpl; try congruence; intros p0 EQ0.
  intros EQ1.
  eapply compose_forward_simulation. apply SimplExprproof.transl_program_correct. apply SimplExprproof.SimplExpr_sepcomp_rel. eauto.
  exact (fst (transf_clight_program_opt_correct _ _ _ EQ1)). 

  split. auto. 
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces. eapply Asm.semantics_determinate.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem transf_c_program_opt_correct:
  forall l p tp,
  transf_c_program_opt l p = OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  intros. 
  apply compose_backward_simulation with (atomic (Cstrategy.semantics p)).
  eapply sd_traces; eapply Asm.semantics_determinate.
  apply factor_backward_simulation. 
  apply Cstrategy.strategy_simulation.
  apply Csem.semantics_single_events.
  eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  exact (snd (transf_cstrategy_program_opt_correct _ _ _ H)).
Qed.
