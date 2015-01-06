Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_linker.
Require Import Maps Maps_linker.
Require Import Integers Floats Values AST Globalenvs.
Require Import Errors Behaviors Compiler Smallstep.
Require Import Language Linker.
Require Import Tree.

Require ProgramLSim Adequacy.

Require SimplExprproof_linker.
Require Selectionproof_linker.
Require Tailcallproof_linker.
Require Inliningproof_linker.
Require Renumberproof_linker.
Require Constpropproof_linker.
Require CSEproof_linker.
Require Deadcodeproof_linker.

Set Implicit Arguments.

(** linker correctness statement *)

Definition linker_correctness :=
  forall ctree asmtree cprog
         (CLINK: Tree.reduce (link_program Language_C) ctree = Some cprog)
         (TRANSF: Tree.Forall2 (fun c a => transf_c_program c = OK a) ctree asmtree),
  exists (asmprog:Asm.program)
         (FS:forward_simulation (Cstrategy.semantics cprog) (Asm.semantics asmprog)),
    Tree.reduce (link_program Language_Asm) asmtree = Some asmprog.

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

Lemma transform_program_link_program
      fT1 fT2 vT
      (tf:(Fundef_common fT1) -> (Fundef_common fT2))
      (p1 p2 p:(mkLanguage (Fundef_common fT1) vT).(progT))
      (q1 q2:(mkLanguage (Fundef_common fT2) vT).(progT))
      (Hp: link_program (mkLanguage (Fundef_common fT1) vT) p1 p2 = Some p)
      (H1: transform_program tf p1 = q1)
      (H2: transform_program tf p2 = q2):
  exists q,
    link_program (mkLanguage (Fundef_common fT2) vT) q1 q2 = Some q /\
    transform_program tf p = q.
Proof.
  admit.
Qed.

Lemma transform_partial_program2_link_program
      (lang_src lang_tgt:Language)
      (tf:lang_src.(fundefT)->res lang_tgt.(fundefT))
      (tv:lang_src.(vT)->res lang_tgt.(vT))
      p1 p2 p q1 q2
      (Hp: link_program lang_src p1 p2 = Some p)
      (H1: transform_partial_program2 tf tv p1 = OK q1)
      (H2: transform_partial_program2 tf tv p2 = OK q2):
  exists q,
    link_program lang_tgt q1 q2 = Some q /\
    transform_partial_program2 tf tv p = OK q.
Proof.
  destruct p1 as [p1 mainp1], p2 as [p2 mainp2], q1 as [q1 mainq1], q2 as [q2 mainq2].
  rewrite transform_partial_program2_augment in *. simpl in *.
  apply transform_partial_augment_program_match in H1. destruct H1 as [[qdefs1 [Hqdefs1 ?]] Hmain1].
  apply transform_partial_augment_program_match in H2. destruct H2 as [[qdefs2 [Hqdefs2 ?]] Hmain2].
  simpl in *. rewrite app_nil_r in *. symmetry in H, H0. subst.
  unfold link_program in *. simpl in *. destruct (Pos.eqb mainp1 mainp2) eqn:Hmainp; [|inv Hp].
  apply Peqb_true_eq in Hmainp. subst.
  admit.
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

Theorem linker_correct: linker_correctness.
Proof.
  repeat intro.

  (* C *)
  unfold transf_c_program in TRANSF. clarify.

  eapply Tree.Forall2_implies in T; [|apply SimplExprproof_linker.SimplExpr_program_lsim].
  eapply Tree.Forall2_reduce in T; eauto;
    [|intros; eapply (@ProgramLSim.link_program_lsim Language_C Language_Clight); eauto].
  Focus 2.
  { intros. destruct ef_src as [[[? ?] ?] [? ?]]. simpl in *. inv H. auto. } (* TODO *)
  Unfocus.
  destruct T as [clight1prog [Hclight1prog Hclight1sim]].
  apply Adequacy.program_sim_forward_simulation in Hclight1sim; auto;
    [|eapply SimplExprproof_linker.mrelT_props; eauto].

  (* Clight *)
  unfold transf_clight_program in TRANSF. clarify.

  eapply Tree.Forall2_reduce in T1; eauto;
    [|eapply (transform_partial_program2_link_program Language_Clight Language_Clight)].
  destruct T1 as [clight2prog [Hclight2prog Hclight2sim]].
  apply SimplLocalsproof.transf_program_correct in Hclight2sim.

  eapply Tree.Forall2_reduce in T0; eauto;
    [|eapply (transform_partial_program2_link_program Language_Clight Language_Csharpminor)].
  destruct T0 as [csharpminorprog [Hsharpminorprog Hsharpminorsim]].
  apply Cshmgenproof.transl_program_correct in Hsharpminorsim.

  eapply Tree.Forall2_reduce in T; eauto;
    [|eapply (transform_partial_program2_link_program Language_Csharpminor Language_Cminor)].
  destruct T as [cminorprog [Hcminorprog Hcminorsim]].
  apply Cminorgenproof.transl_program_correct in Hcminorsim.

  (* Cminor *)
  unfold transf_cminor_program in TRANSF. clarify.

  eapply Tree.Forall2_implies in T0; [|apply Selectionproof_linker.Selection_program_lsim].
  eapply Tree.Forall2_reduce in T0; eauto;
    [|intros; eapply (@ProgramLSim.link_program_lsim Language_Cminor Language_CminorSel); eauto].
  destruct T0 as [cminorselprog [Hcminorselprog Hcminorselsim]].
  apply Adequacy.program_sim_forward_simulation in Hcminorselsim; auto;
    [|eapply Selectionproof_linker.mrelT_props; eauto].

  eapply Tree.Forall2_reduce in T; eauto;
    [|eapply (transform_partial_program2_link_program Language_CminorSel Language_RTL)].
  destruct T as [rtlprog0 [Hrtlprog0 Hrtlsim0]].
  apply RTLgenproof.transf_program_correct in Hrtlsim0.

  (* RTL *)
  unfold transf_rtl_program in TRANSF. clarify.

  eapply Tree.Forall2_implies in T19; [|apply Tailcallproof_linker.Tailcall_program_lsim].
  eapply Tree.Forall2_reduce in T19; eauto;
    [|intros; eapply (@ProgramLSim.link_program_lsim Language_RTL Language_RTL); eauto].
  destruct T19 as [rtlprog1 [Hrtlprog1 Hrtlsim1]].
  apply Adequacy.program_sim_forward_simulation in Hrtlsim1; auto;
    [|eapply Tailcallproof_linker.mrelT_props; eauto].
  
  eapply Tree.Forall2_implies in T17; [|apply Inliningproof_linker.Inlining_program_lsim].
  eapply Tree.Forall2_reduce in T17; eauto;
    [|intros; eapply (@ProgramLSim.link_program_lsim Language_RTL Language_RTL); eauto].
  destruct T17 as [rtlprog2 [Hrtlprog2 Hrtlsim2]].
  apply Adequacy.program_sim_forward_simulation in Hrtlsim2; auto;
    [|eapply Inliningproof_linker.mrelT_props; eauto].

  eapply Tree.Forall2_implies in T15; [|apply Renumberproof_linker.Renumber_program_lsim].
  eapply Tree.Forall2_reduce in T15; eauto;
    [|intros; eapply (@ProgramLSim.link_program_lsim Language_RTL Language_RTL); eauto].
  destruct T15 as [rtlprog3 [Hrtlprog3 Hrtlsim3]].
  apply Adequacy.program_sim_forward_simulation in Hrtlsim3; auto;
    [|eapply Renumberproof_linker.mrelT_props; eauto].

  eapply Tree.Forall2_implies in T13; [|apply Constpropproof_linker.Constprop_program_lsim].
  eapply Tree.Forall2_reduce in T13; eauto;
    [|intros; eapply (@ProgramLSim.link_program_lsim Language_RTL Language_RTL); eauto].
  destruct T13 as [rtlprog4 [Hrtlprog4 Hrtlsim4]].
  apply Adequacy.program_sim_forward_simulation in Hrtlsim4; auto;
    [|eapply Constpropproof_linker.mrelT_props; eauto].

  eapply Tree.Forall2_implies in T11; [|apply Renumberproof_linker.Renumber_program_lsim].
  eapply Tree.Forall2_reduce in T11; eauto;
    [|intros; eapply (@ProgramLSim.link_program_lsim Language_RTL Language_RTL); eauto].
  destruct T11 as [rtlprog5 [Hrtlprog5 Hrtlsim5]].
  apply Adequacy.program_sim_forward_simulation in Hrtlsim5; auto;
    [|eapply Renumberproof_linker.mrelT_props; eauto].

  eapply Tree.Forall2_implies in T9; [|apply CSEproof_linker.CSE_program_lsim].
  eapply Tree.Forall2_reduce in T9; eauto;
    [|intros; eapply (@ProgramLSim.link_program_lsim Language_RTL Language_RTL); eauto].
  destruct T9 as [rtlprog6 [Hrtlprog6 Hrtlsim6]].
  apply Adequacy.program_sim_forward_simulation in Hrtlsim6; auto;
    [|eapply CSEproof_linker.mrelT_props; eauto].

  eapply Tree.Forall2_implies in T7; [|apply Deadcodeproof_linker.Deadcode_program_lsim].
  eapply Tree.Forall2_reduce in T7; eauto;
    [|intros; eapply (@ProgramLSim.link_program_lsim Language_RTL Language_RTL); eauto].
  destruct T7 as [rtlprog7 [Hrtlprog7 Hrtlsim7]].
  apply Adequacy.program_sim_forward_simulation in Hrtlsim7; auto;
    [|eapply Deadcodeproof_linker.mrelT_props; eauto].

  eapply Tree.Forall2_reduce in T5; eauto;
    [|eapply (transform_partial_program2_link_program Language_RTL Language_LTL)].
  destruct T5 as [ltlprog0 [Hltlprog0 Hltlsim0]].
  apply Allocproof.transf_program_correct in Hltlsim0.

  eapply Tree.Forall2_reduce in T3; eauto;
    [|eapply (transform_program_link_program)].
  destruct T3 as [ltlprog1 [Hltlprog1 Hltlsim1]]. subst.
  generalize (Tunnelingproof.transf_program_correct ltlprog0) as Hltlsim1. intro.

  eapply Tree.Forall2_reduce in T2; eauto;
    [|eapply (transform_partial_program2_link_program Language_LTL Language_Linear)].
  destruct T2 as [linearprog0 [Hlinearprog0 Hlinearsim0]].
  apply Linearizeproof.transf_program_correct in Hlinearsim0.

  eapply Tree.Forall2_reduce in T1; eauto;
    [|eapply (transform_program_link_program)].
  destruct T1 as [linearprog1 [Hlinearprog1 Hlinearsim1]]. subst.
  generalize (CleanupLabelsproof.transf_program_correct linearprog0) as Hlinearsim1. intro.

  eapply Tree.Forall2_reduce in T0; eauto;
    [|eapply (transform_partial_program2_link_program Language_Linear Language_Mach)].
  destruct T0 as [machprog [Hmachprog Hmachsim]].
  eapply Stackingproof.transf_program_correct in Hmachsim; eauto;
    [|eexact Asmgenproof.return_address_exists; eassumption].

  eapply Tree.Forall2_reduce in TRANSF; eauto;
    [|eapply (transform_partial_program2_link_program Language_Mach Language_Asm)].
  destruct TRANSF as [asmprog [Hasmprog Hasmsim]].
  eapply Asmgenproof.transf_program_correct in Hasmsim; eauto.

  (* epilogue *)
  exists asmprog. eexists; auto.
  repeat (eapply compose_forward_simulation; [|eauto; fail]).  
  eapply compose_forward_simulation; [|apply rtl_sem_implies1; fail].
  repeat (eapply compose_forward_simulation; [|eauto; fail]).
  eapply compose_forward_simulation; [|apply rtl_sem_implies2; fail].
  repeat (eapply compose_forward_simulation; [|eauto; fail]).
  eapply compose_forward_simulation; [|apply cminorsel_sem_implies1; fail].
  repeat (eapply compose_forward_simulation; [|eauto; fail]).
  eapply compose_forward_simulation; [|apply cminor_sem_implies2; fail].
  repeat (eapply compose_forward_simulation; [|eauto; fail]).
  eapply compose_forward_simulation; [|apply clight1_sem_implies1; fail].
  repeat (eapply compose_forward_simulation; [|eauto; fail]).
  apply c_sem_implies2.
Qed.
