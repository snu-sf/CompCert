Require Import Axioms.
Require Import RelationClasses.
Require String.
Require Import Coqlib CoqlibExtra.
Require Import Maps MapsExtra.
Require Import Integers Floats Values AST Globalenvs.
Require Import Errors Behaviors Compiler Smallstep.
Require Import Language Linker.
Require Import Tree.
Require Import LinkerBasicproof.
Require Import SepcompRel.

Require Import Tailcallproof.
Require Import SimplExprproof.
Require Import Selectionproof.
Require Import Inliningproof.
Require Import Constpropproof.
Require Import CSEproof.
Require Import Deadcodeproof.
Require Import Asmgenproof.
Require Import Allocproof.
Require Import Linearizeproof.
Require Import Stackingproof.
Require Import RTLgenproof.
Require Import Cshmgenproof.
Require Import Cminorgenproof.
Require Import SimplLocalsproof.
Require Import SimplExprproof.


Set Implicit Arguments.

Lemma Asmgen_sig:
  forall (f1 : F_Mach) (f2 : F_Asm),
    Asmgen.transf_function f1 = OK f2 -> F_sig F_Mach f1 = F_sig F_Asm f2.
Proof.
  intros.
  unfold Asmgen.transf_function in H. monadInv H.
  unfold Asmgen.transl_function in EQ. monadInv EQ.
  sig_clarify. auto.
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
  destruct f1, f2; inv H1; inv H2; inv Hlink; simpl in *; sig_clarify.
  - destruct (tf i2) eqn:Hi2; inv EQ.
    eapply globfun_linkable_ei; simpl; eauto.
    rewrite Hsig. erewrite Htf; eauto.
  - eapply globfun_linkable_ee; simpl; eauto.
Qed.

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

Lemma total_if_link_program
      (fT:F Sig_signature) vT
      (p1 p2 p:(mkLanguage (Fundef_common fT) vT).(progT))
      (q1 q2:(mkLanguage (Fundef_common fT) vT).(progT))
      flag transf
      (TRANSF:
         forall (Hp: link_program (mkLanguage (Fundef_common fT) vT) p1 p2 = Some p)
                (H1: transf p1 = q1)
                (H2: transf p2 = q2),
         exists q,
           link_program (mkLanguage (Fundef_common fT) vT) q1 q2 = Some q /\
           transf p = q)
      (Hp: link_program (mkLanguage (Fundef_common fT) vT) p1 p2 = Some p)
      (H1: total_if flag transf p1 = q1)
      (H2: total_if flag transf p2 = q2):
  exists q,
    link_program (mkLanguage (Fundef_common fT) vT) q1 q2 = Some q /\
    total_if flag transf p = q.
Proof.
  unfold total_if in *. destruct (flag tt).
  - apply TRANSF; auto.
  - subst. eexists. split; eauto.
Qed.

Lemma Tree_Forall2_total_if
      lang flag transf (ptree tptree:Tree.t lang.(progT))
      (FORALL: Tree.Forall2 (fun p tp => total_if flag transf p = tp) ptree tptree):
  ptree = tptree \/
  Tree.Forall2 (fun p tp => transf p = tp) ptree tptree.
Proof.
  unfold total_if in *. destruct (flag tt).
  { right. auto. }
  left. induction FORALL; subst; auto.
Qed.

Lemma Tree_Forall2_partial_if
      lang flag transf (ptree tptree:Tree.t lang.(progT))
      (FORALL: Tree.Forall2 (fun p tp => partial_if flag transf p = OK tp) ptree tptree):
  ptree = tptree \/
  Tree.Forall2 (fun p tp => transf p = OK tp) ptree tptree.
Proof.
  unfold partial_if in *. destruct (flag tt).
  { right. auto. }
  left. induction FORALL; subst; auto. inv Hpred. auto.
Qed.

Lemma partial_if_link_program
      (fT:F Sig_signature) vT
      (p1 p2 p:(mkLanguage (Fundef_common fT) vT).(progT))
      (q1 q2:(mkLanguage (Fundef_common fT) vT).(progT))
      flag transf
      (TRANSF:
         forall (Hp: link_program (mkLanguage (Fundef_common fT) vT) p1 p2 = Some p)
                (H1: transf p1 = OK q1)
                (H2: transf p2 = OK q2),
         exists q,
           link_program (mkLanguage (Fundef_common fT) vT) q1 q2 = Some q /\
           transf p = OK q)
      (Hp: link_program (mkLanguage (Fundef_common fT) vT) p1 p2 = Some p)
      (H1: partial_if flag transf p1 = OK q1)
      (H2: partial_if flag transf p2 = OK q2):
  exists q,
    link_program (mkLanguage (Fundef_common fT) vT) q1 q2 = Some q /\
    partial_if flag transf p = OK q.
Proof.
  unfold partial_if in *. destruct (flag tt).
  - apply TRANSF; auto.
  - inv H1. inv H2. eexists. split; eauto.
Qed.

Lemma linker_correct_determinate_forward
        ctree asmtree cprog
        (CLINK: Tree.reduce (link_program Language.Language_C) ctree = Some cprog)
        (TRANSF: Tree.Forall2 (fun c a => transf_c_program c = OK a) ctree asmtree):
  exists (asmprog:Asm.program)
    (_:forward_simulation (Cstrategy.semantics cprog) (Asm.semantics asmprog)),
    Tree.reduce (link_program Language.Language_Asm) asmtree = Some asmprog.
Proof.
  repeat intro.

  (* C *)
  unfold transf_c_program in TRANSF. clarify.

  eapply Tree.Forall2_implies in T; [|apply SimplExprproof.SimplExpr_sepcomp_rel].
  eapply Tree.Forall2_reduce in T; eauto;
    [|eapply (@link_program_sepcomp_rel Language.Language_C Language.Language_Clight id)]; simplify;
    [|apply SimplExpr_sig; auto].
  destruct T as [clightprog [Hclightprog Hclightsim]].
  apply SimplExprproof.transl_program_correct in Hclightsim.

  (* Clight *)
  unfold transf_clight_program in TRANSF. clarify.

  eapply Tree.Forall2_reduce in T1; eauto;
    [|eapply (transform_partial_program2_link_program Language.Language_Clight Language.Language_Clight)];
    [|apply SimplLocals_sig].
  destruct T1 as [clight2prog [Hclight2prog Hclight2sim]].
  apply SimplLocalsproof.transf_program_correct in Hclight2sim.

  eapply Tree.Forall2_reduce in T0; eauto;
    [|eapply (transform_partial_program2_link_program Language.Language_Clight Language.Language_Csharpminor)];
    [|apply Cshmgen_sig].
  destruct T0 as [csharpminorprog [Hsharpminorprog Hsharpminorsim]].
  apply Cshmgenproof.transl_program_correct in Hsharpminorsim.

  eapply Tree.Forall2_reduce in T; eauto;
    [|eapply (transform_partial_program2_link_program Language.Language_Csharpminor Language.Language_Cminor)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply Cminorgen_sig].
  destruct T as [cminorprog [Hcminorprog Hcminorsim]].
  apply Cminorgenproof.transl_program_correct in Hcminorsim.

  (* Cminor *)
  unfold transf_cminor_program in TRANSF. clarify.

  exploit Tree.Forall2_implies. apply Selectionproof.Selection_check_helpers. eauto.
  intro T_CH. apply Tree.Forall2_Forall in T_CH.
    
  eapply Tree.Forall_reduce in T_CH; [| apply Selectionproof.link_program_check_helpers|eauto].
  eapply Tree.Forall2_implies in T0; [|apply Selectionproof.Selection_sepcomp_rel].

  eapply Tree.Forall2_reduce in T0; eauto;
    [|eapply (@link_program_sepcomp_rel Language.Language_Cminor Language.Language_CminorSel id)]; simplify;
    [|eapply Selection_sig; eauto].

  destruct T0 as [cminorselprog [Hcminorselprog Hcminorselsim]].

  apply Selectionproof.transf_program_correct in Hcminorselsim;
    eauto using Selectionproof.check_helpers_correct.

  eapply Tree.Forall2_reduce in T; eauto;
    [|eapply (transform_partial_program2_link_program Language.Language_CminorSel Language.Language_RTL)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply RTLgen_sig].
  destruct T as [rtlprog0 [Hrtlprog0 Hrtlsim0]].
  apply RTLgenproof.transf_program_correct in Hrtlsim0.

  (* RTL *)
  unfold transf_rtl_program in TRANSF. clarify.
  repeat match goal with
           | [H: Tree.Forall2 (fun _ _ => total_if _ _ _ = _) _ _ |- _] =>
             apply (@Tree_Forall2_total_if Language_RTL) in H; simpl in H
           | [H: Tree.Forall2 (fun _ _ => partial_if _ _ _ = _) _ _ |- _] =>
             apply (@Tree_Forall2_partial_if Language_RTL) in H; simpl in H
         end.

  Lemma elim_or
    (P1 P2 C:Prop)
    (H: P1 \/ P2)
    (H1: P1 -> C)
    (H2: P2 -> C):
    C.
  Proof. destruct H; auto. Qed.
  idtac.

  Lemma Tree_reduce_sim_identity
        ptree tptree p
        (EQ: ptree = tptree)
        (REDUCE: Tree.reduce (link_program Language_RTL) ptree = Some p):
    exists tp (SIM: forward_simulation (RTL.semantics p) (RTL.semantics tp)),
      Tree.reduce (link_program Language_RTL) tptree = Some tp.
  Proof. subst. exists p, (forward_simulation_identity _). auto. Qed.
  idtac.
  
  exploit (elim_or T19 (@Tree_reduce_sim_identity _ _ rtlprog0)); auto.
  { intro X. eapply Tree.Forall2_reduce in X; eauto;
      [|eapply transform_program_link_program];
      [|apply Tailcall_sig].
    destruct X as [? [? ?]]. subst. intros.
    exists _, (Tailcallproof.transf_program_correct rtlprog0). auto.
  }
  clear T19. intros [rtlprog1 [Hrtlprog1 Hrtlsim1]].

  eapply Tree.Forall2_implies in T17; [|apply Inliningproof.Inlining_sepcomp_rel].
  eapply Tree.Forall2_reduce in T17; eauto; [|eapply (@link_program_sepcomp_rel Language.Language_RTL Language.Language_RTL id)]; simplify;
    [|eapply Inlining_sig; eauto].
  destruct T17 as [rtlprog2 [Hrtlprog2 Hrtlsim2]].
  apply Inliningproof.transf_program_correct in Hrtlsim2.

  eapply Tree.Forall2_reduce in T15; eauto;
    [|eapply transform_program_link_program; auto].
  destruct T15 as [rtlprog3 [Hrtlprog3 Hrtlsim3]]. subst.
  generalize (Renumberproof.transf_program_correct rtlprog2) as Hrtlsim3. intro.

  exploit (elim_or T13 (@Tree_reduce_sim_identity _ _ (Renumber.transf_program rtlprog2))); auto.
  { intro X. eapply Tree.Forall2_implies in X; [|apply Constpropproof.Constprop_sepcomp_rel].
    eapply Tree.Forall2_reduce in X; eauto; [|eapply (@link_program_sepcomp_rel Language.Language_RTL Language.Language_RTL id)]; simplify.
    destruct X as [rtlprog4 [Hrtlprog4 Hrtlsim4]].
    apply Constpropproof.transf_program_correct in Hrtlsim4.
    exists _, Hrtlsim4. auto.
  }
  clear T13. intros [rtlprog4 [Hrtlprog4 Hrtlsim4]].

  exploit (elim_or T11 (@Tree_reduce_sim_identity _ _ rtlprog4)); auto.
  { intro X. eapply Tree.Forall2_reduce in X; eauto; [|eapply transform_program_link_program; auto].
    destruct X as [rtlprog5 [Hrtlprog5 Hrtlsim5]]. subst.
    exists _, (Renumberproof.transf_program_correct rtlprog4). auto.
  }
  clear T11. intros [rtlprog5 [Hrtlprog5 Hrtlsim5]].

  exploit (elim_or T9 (@Tree_reduce_sim_identity _ _ rtlprog5)); auto.
  { intro X. eapply Tree.Forall2_implies in X; [|apply CSEproof.CSE_sepcomp_rel].
    eapply Tree.Forall2_reduce in X; eauto;
      [|eapply (@link_program_sepcomp_rel Language.Language_RTL Language.Language_RTL id)]; simplify;
      [|eapply CSE_sig; eauto].
    destruct X as [rtlprog6 [Hrtlprog6 Hrtlsim6]].
    apply CSEproof.transf_program_correct in Hrtlsim6.
    exists _, Hrtlsim6. auto.
  }
  clear T9. intros [rtlprog6 [Hrtlprog6 Hrtlsim6]].

  exploit (elim_or T7 (@Tree_reduce_sim_identity _ _ rtlprog6)); auto.
  { intro X. eapply Tree.Forall2_implies in X; [|apply Deadcodeproof.Deadcode_sepcomp_rel].
    eapply Tree.Forall2_reduce in X; eauto;
      [|eapply (@link_program_sepcomp_rel Language.Language_RTL Language.Language_RTL id)]; simplify;
      [|eapply Deadcode_sig; eauto].
    destruct X as [rtlprog7 [Hrtlprog7 Hrtlsim7]].
    apply Deadcodeproof.transf_program_correct in Hrtlsim7.
    exists _, Hrtlsim7. auto.
  }
  clear T7. intros [rtlprog7 [Hrtlprog7 Hrtlsim7]].

  eapply Tree.Forall2_reduce in T5; eauto;
    [|eapply (transform_partial_program2_link_program Language.Language_RTL Language.Language_LTL)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply Allocation_sig].
  destruct T5 as [ltlprog0 [Hltlprog0 Hltlsim0]].
  apply Allocproof.transf_program_correct in Hltlsim0.

  eapply Tree.Forall2_reduce in T3; eauto;
    [|eapply transform_program_link_program; auto].
  destruct T3 as [ltlprog1 [Hltlprog1 Hltlsim1]]. subst.
  generalize (Tunnelingproof.transf_program_correct ltlprog0) as Hltlsim1. intro.

  eapply Tree.Forall2_reduce in T2; eauto;
    [|eapply (transform_partial_program2_link_program Language.Language_LTL Language.Language_Linear)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply Linearize_sig].
  destruct T2 as [linearprog0 [Hlinearprog0 Hlinearsim0]].
  apply Linearizeproof.transf_program_correct in Hlinearsim0.

  eapply Tree.Forall2_reduce in T1; eauto;
    [|eapply transform_program_link_program; auto].
  destruct T1 as [linearprog1 [Hlinearprog1 Hlinearsim1]]. subst.
  generalize (CleanupLabelsproof.transf_program_correct linearprog0) as Hlinearsim1. intro.

  eapply Tree.Forall2_reduce in T0; eauto;
    [|eapply (transform_partial_program2_link_program Language.Language_Linear Language.Language_Mach)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply Stacking_sig].
  destruct T0 as [machprog [Hmachprog Hmachsim]].
  eapply Stackingproof.transf_program_correct in Hmachsim; eauto;
    [|eexact Asmgenproof.return_address_exists; eassumption].

  eapply Tree.Forall2_reduce in TRANSF; eauto;
    [|eapply (transform_partial_program2_link_program Language.Language_Mach Language.Language_Asm)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply Asmgen_sig].
  destruct TRANSF as [asmprog [Hasmprog Hasmsim]].
  eapply Asmgenproof.transf_program_correct in Hasmsim; eauto.

  (* epilogue *)
  exists asmprog. eexists; auto.
  repeat (auto; try (eapply compose_forward_simulation; [|eauto; fail])).
Qed.

Lemma linker_correct_determinate
        ctree asmtree cprog
        (CLINK: Tree.reduce (link_program Language.Language_C) ctree = Some cprog)
        (TRANSF: Tree.Forall2 (fun c a => transf_c_program c = OK a) ctree asmtree):
  exists (asmprog:Asm.program)
    (_:backward_simulation (atomic (Cstrategy.semantics cprog)) (Asm.semantics asmprog)),
    Tree.reduce (link_program Language.Language_Asm) asmtree = Some asmprog.
Proof.
  exploit linker_correct_determinate_forward; eauto.
  intros [asmprog [Hsim Hasmprog]]. exists asmprog.
  eexists; auto.
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces. eapply Asm.semantics_determinate.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem linker_correct
        ctree asmtree cprog
        (CLINK: Tree.reduce (link_program Language.Language_C) ctree = Some cprog)
        (TRANSF: Tree.Forall2 (fun c a => transf_c_program c = OK a) ctree asmtree):
  exists (asmprog:Asm.program)
    (_:backward_simulation (Csem.semantics cprog) (Asm.semantics asmprog)),
    Tree.reduce (link_program Language.Language_Asm) asmtree = Some asmprog.
Proof.
  exploit linker_correct_determinate; eauto.
  intros [asmprog [Hsim Hasmprog]]. exists asmprog.
  eexists; eauto.
  apply compose_backward_simulation with (atomic (Cstrategy.semantics cprog)).
  eapply sd_traces; eapply Asm.semantics_determinate.
  apply factor_backward_simulation. 
  apply Cstrategy.strategy_simulation.
  apply Csem.semantics_single_events.
  eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  exact Hsim.
Qed.
