Require Import Axioms.
Require Import RelationClasses.
Require String.
Require Import Coqlib CoqlibExtra.
Require Import Maps MapsExtra.
Require Import Integers Floats Values AST Globalenvs.
Require Import Errors Behaviors Smallstep.
Require Import Language Linker.
Require Import Tree.
Require Import LinkerBasicproof Sig.
Require Import SepcompRel.

Require SimplExprproof.
Require Selectionproof.
Require Tailcallproof.
Require Inliningproof.
Require Renumberproof.
Require Constpropproof.
Require CSEproof.
Require Deadcodeproof.
Require Import Compiler.
Require Import CompilerExtra.
Require Import sflib.

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

Inductive optimize_rtl_program: forall (rtl: RTL.program) (ortl: RTL.program), Prop:=
| rtlopt_tailcall: forall r1, optimize_rtl_program r1 (Tailcall.transf_program r1)
| rtlopt_inlining: forall r1 r1' (TR_OK: Inlining.transf_program r1 = OK r1'),
                     optimize_rtl_program r1 r1'
| rtlopt_renumber: forall r1, optimize_rtl_program r1 (Renumber.transf_program r1)
| rtlopt_constprop: forall r1, optimize_rtl_program r1 (Constprop.transf_program r1)
| rtlopt_cse: forall r1 r1' (TR_OK: CSE.transf_program r1 = OK r1'),
                optimize_rtl_program r1 r1'
| rtlopt_deadcode: forall r1 r1' (TR_OK: Deadcode.transf_program r1 = OK r1'),
                     optimize_rtl_program r1 r1'.

Hint Constructors optimize_rtl_program.

Definition rtl_opt_tree := Tree.change_one optimize_rtl_program.

Lemma rtl_opt_tree_destruct:
  forall tr tr' (ROPTT: rtl_opt_tree tr tr'),
    << TAILCALL: Tree.Forall2 (fun p1 p2 => (Tailcall.transf_program p1 = p2) \/ p1 = p2) tr tr' >>
    \/  << INLINING: Tree.Forall2 (fun p1 p2 => (Inlining.transf_program p1 = OK p2) \/ p1 = p2) tr tr' >>
    \/  << RENUMBER: Tree.Forall2 (fun p1 p2 => (Renumber.transf_program p1 = p2) \/ p1 = p2) tr tr' >>
    \/  << CONSTPROP: Tree.Forall2 (fun p1 p2 => (Constprop.transf_program p1 = p2) \/ p1 = p2) tr tr' >>
    \/  << CSE: Tree.Forall2 (fun p1 p2 => (CSE.transf_program p1 = OK p2) \/ p1 = p2) tr tr' >>
    \/  << DEADCODE: Tree.Forall2 (fun p1 p2 => (Deadcode.transf_program p1 = OK p2) \/ p1 = p2) tr tr' >>.
Proof.
  intros. induction ROPTT.
  - inv REL; [|right|right;right|right;right;right|right;right;right;right |right;right;right;right;right ]; [left|left|left|left|left| ]; constructor; auto.
  - des; [|right|right;right|right;right;right|right;right;right;right |right;right;right;right;right ]; [left|left|left|left|left|];
    (constructor; auto; eapply Tree.Forall2_implies;
    [ intros; right; apply H | apply Tree.Tree_Forall2_eq_same]).
  - des; [|right|right;right|right;right;right|right;right;right;right |right;right;right;right;right ]; [left|left|left|left|left|];
    (constructor; auto; eapply Tree.Forall2_implies;
    [ intros; right; apply H | apply Tree.Tree_Forall2_eq_same]).
Qed.

Lemma rtl_opt_tree_reduce_simulation:
  forall tr tr' rtlprog
         (ROPT1T: rtl_opt_tree tr tr')
         (REDUCE: Tree.reduce (link_program Language.Language_RTL) tr = Some rtlprog),
  exists rtlprog'
    (Hrtlsim': forward_simulation (RTL.semantics rtlprog) (RTL.semantics rtlprog')),
    << Hrtlprog': Tree.reduce (link_program Language.Language_RTL) tr' = Some rtlprog' >>.
Proof.
  intros.
  apply rtl_opt_tree_destruct in ROPT1T. des.
  - eapply Tree.Forall2_implies in TAILCALL; [|apply Tailcallproof.Tailcall_sepcomp_rel].
    eapply Tree.Forall2_reduce in TAILCALL; eauto; [|eapply (@link_program_sepcomp_rel Language.Language_RTL Language.Language_RTL id)]; simplify.
    + destruct TAILCALL as [rtlprog1 [Hrtlprog1 Hrtlsim1]].
      apply Tailcallproof.transf_program_correct in Hrtlsim1. eexists. eauto.
    + des; subst; [apply Tailcall_sig | auto].
  - eapply Tree.Forall2_implies in INLINING; [|apply Inliningproof.Inlining_sepcomp_rel].
    eapply Tree.Forall2_reduce in INLINING; eauto; [|eapply (@link_program_sepcomp_rel Language.Language_RTL Language.Language_RTL id)]; simplify.
    + destruct INLINING as [rtlprog1 [Hrtlprog1 Hrtlsim1]].
      apply Inliningproof.transf_program_correct in Hrtlsim1. eexists. eauto.
    + des; subst; [eapply Inlining_sig|]; eauto.
  - eapply Tree.Forall2_implies in RENUMBER; [|apply Renumberproof.Renumber_sepcomp_rel].
    eapply Tree.Forall2_reduce in RENUMBER; eauto; [|eapply (@link_program_sepcomp_rel Language.Language_RTL Language.Language_RTL id)]; simplify.
    + destruct RENUMBER as [rtlprog1 [Hrtlprog1 Hrtlsim1]].
      apply Renumberproof.transf_program_correct in Hrtlsim1. eexists. eauto.
    + des; subst; auto.
  - eapply Tree.Forall2_implies in CONSTPROP; [|apply Constpropproof.Constprop_sepcomp_rel].
    eapply Tree.Forall2_reduce in CONSTPROP; eauto; [|eapply (@link_program_sepcomp_rel Language.Language_RTL Language.Language_RTL id)]; simplify.
    + destruct CONSTPROP as [rtlprog1 [Hrtlprog1 Hrtlsim1]].
      apply Constpropproof.transf_program_correct in Hrtlsim1. eexists. eauto.
    + des; subst; auto.
  - eapply Tree.Forall2_implies in CSE; [|apply CSEproof.CSE_sepcomp_rel].
    eapply Tree.Forall2_reduce in CSE; eauto; [|eapply (@link_program_sepcomp_rel Language.Language_RTL Language.Language_RTL id)]; simplify.
    + destruct CSE as [rtlprog1 [Hrtlprog1 Hrtlsim1]].
      apply CSEproof.transf_program_correct in Hrtlsim1. eexists. eauto.
    + des; subst; [eapply CSE_sig|]; eauto.
  - eapply Tree.Forall2_implies in DEADCODE; [|apply Deadcodeproof.Deadcode_sepcomp_rel].
    eapply Tree.Forall2_reduce in DEADCODE; eauto; [|eapply (@link_program_sepcomp_rel Language.Language_RTL Language.Language_RTL id)]; simplify.
    + destruct DEADCODE as [rtlprog1 [Hrtlprog1 Hrtlsim1]].
      apply Deadcodeproof.transf_program_correct in Hrtlsim1. eexists. eauto.
    + des; subst; [eapply Deadcode_sig|]; eauto.
Qed.

Lemma optimize_rtl_program_reduce_simulation:
  forall (rtlprog: RTL.program)
         (tr1 tr2: Tree.t RTL.program)
         (REDUCE: Tree.reduce (link_program Language.Language_RTL) tr1 = Some rtlprog)
         (ROPT: rtc rtl_opt_tree tr1 tr2),
  exists rtlprog'
         (Hrtlsim': forward_simulation (RTL.semantics rtlprog) (RTL.semantics rtlprog')),
    << Hrtlprog': Tree.reduce (link_program Language.Language_RTL) tr2 = Some rtlprog' >>.
Proof.
  intros. generalize dependent rtlprog.
  induction ROPT; intros.
  - exploit rtl_opt_tree_reduce_simulation; eauto.
  - exists rtlprog. exists (forward_simulation_identity (RTL.semantics rtlprog)); eauto.
  - exploit IHROPT1; eauto. intros. des.
    exploit IHROPT2; eauto. intros. des.
    exists rtlprog'0.
    exists (compose_forward_simulation Hrtlsim' Hrtlsim'0); eauto.
Qed.

Lemma rtl_exists_frtl:
  forall l rtlprog n asmprog
         (TRANS: transf_rtl_program_opt n l rtlprog = OK asmprog),
  exists frtlprog,
    (rtc optimize_rtl_program) rtlprog frtlprog
    /\ transf_rtl_program_to_asm_opt (OK frtlprog) = OK asmprog.
Proof.
  intros l. induction l; intros.
  - unfold transf_rtl_program_opt in TRANS.
    unfold transf_rtl_program_opt' in TRANS.
    esplits; eauto.
  - unfold transf_rtl_program_opt in TRANS.
    unfold transf_rtl_program_opt' in TRANS; fold transf_rtl_program_opt' in TRANS.
    destruct a; destruct r;
    unfold print in TRANS;
    simpl in TRANS;
    unfold total_if, partial_if, time in TRANS;
    destruct (b tt); try (by apply IHl in TRANS; eauto);
    (match goal with [H: transf_rtl_program_opt' _ _ (?tr ?p) = _ |- _] =>
                     destruct (tr p) eqn:TRRES;
                     [|rewrite transf_rtl_program_opt'_error in H; inv H] end;
     apply IHl in TRANS; des; inv TRRES;
     match goal with [H: rtc optimize_rtl_program ?mp ?tp |- _] =>
                     assert (TRANS': optimize_rtl_program rtlprog mp); try (by eauto) end;
     esplits; [econs 3; [econs 1; apply TRANS'| apply TRANS] | eauto]).
Qed.

Lemma optimized_singleton_tree: forall p1 p2,
            rtc optimize_rtl_program p1 p2 ->
            rtc rtl_opt_tree (Tree.Tree_singleton p1) (Tree.Tree_singleton p2).
Proof. i. induction H; [econs; econs|econs 2|econs 3]; eauto. Qed.

Lemma rtl_tree_exists_frtl_tree:
  forall rtltree asmtree rtlprog
         (LINK: Tree.reduce (link_program Language_RTL) rtltree = Some rtlprog)
         (T: Tree.Forall2 (fun a b => exists n, transf_rtl_program_opt n (fst b) a = OK (snd b)) rtltree asmtree),
  exists frtltree,
    rtc rtl_opt_tree rtltree frtltree
    /\ Tree.Forall2 (fun a b => transf_rtl_program_to_asm_opt (OK a) = OK (snd b)) frtltree asmtree.
Proof.
  intros rtltree.
  induction rtltree; intros.
  - inv T. des.
    eapply rtl_exists_frtl in Hpred. des.
    exists (Tree.Tree_singleton frtlprog).
    split; [| econs; eauto].
    apply optimized_singleton_tree; eauto.
  - apply Tree.reduce_composite in LINK. des. inv T.
    eapply IHrtltree1 in FRED; eauto. des.
    eapply IHrtltree2 in SRED; eauto. des.
    esplits; [|econs; eauto].
    econs 3.
    + eapply Tree.rtc_change_one_attach_left; eauto.
    + eapply Tree.rtc_change_one_attach_right; eauto.
Qed.

Lemma rtl_exists_forward_simulation:
  forall p asmtree n
         (rtlprog : RTL.program)
         (Hrtlprog : Tree.reduce (link_program Language_RTL) p = Some rtlprog)
         (T : Tree.Forall2
                (fun (a : RTL.program) (b : opt_list * Asm.program) =>
                   transf_rtl_program_opt n (fst b) a = OK (snd b)) p asmtree),
  exists rtltree rtlprog'
         (_: forward_simulation (RTL.semantics rtlprog) (RTL.semantics rtlprog')),
    Tree.reduce (link_program Language_RTL) rtltree = Some rtlprog'
    /\ Tree.Forall2 (fun a b => transf_rtl_program_to_asm_opt (OK a) = OK (snd b)) rtltree asmtree.
Proof.
  intros.
  exploit rtl_tree_exists_frtl_tree; eauto.
  { eapply Tree.Forall2_implies; eauto.
    i. exists n. eauto. }
  i; des.
  exploit optimize_rtl_program_reduce_simulation; eauto. i; des.
  esplits; eauto.
Qed.

Lemma asmtree_drop_flag:
  forall mtree fasmtree
         (T: Tree.Forall2 (fun (a : Mach.program) (b : opt_list * Asm.program) =>
                             Asmgen.transf_program a = OK (snd b)) mtree fasmtree),
  exists (asmtree: Tree.t Asm.program),
    Tree.Forall2 (fun a b => Asmgen.transf_program a = OK b) mtree asmtree
    /\ Tree.map snd fasmtree = asmtree.
Proof.
  intros.
  exists (Tree.map snd fasmtree).
  split; eauto.
  generalize dependent mtree.
  induction fasmtree; intros.
  - inv T. econs. eauto.
  - inv T. apply IHfasmtree1 in H0. apply IHfasmtree2 in H3.
    unfold Tree.map; fold Tree.map.
    econs; eauto.
Qed.

Lemma linker_correct_determinate_forward_optd
        ctree asmtree cprog
        (CLINK: Tree.reduce (link_program Language.Language_C) ctree = Some cprog)
        (TRANSF: Tree.Forall2 (fun s t => transf_c_program_opt (fst t) s = OK (snd t)) ctree asmtree):
  exists (asmprog:Asm.program)
    (_:forward_simulation (Cstrategy.semantics cprog) (Asm.semantics asmprog)),
    Tree.reduce (link_program Language.Language_Asm) (Tree.map snd asmtree) = Some asmprog.
Proof.
  (* C *)
  unfold transf_c_program_opt in TRANSF. clarify.

  eapply Tree.Forall2_implies in T; [|apply SimplExprproof.SimplExpr_sepcomp_rel].
  eapply Tree.Forall2_reduce in T; eauto;
    [|eapply (@link_program_sepcomp_rel Language.Language_C Language.Language_Clight id)]; simplify;
    [|apply SimplExpr_sig; auto].
  destruct T as [clightprog [Hclightprog Hclightsim]].
  apply SimplExprproof.transl_program_correct in Hclightsim.

  (* Clight *)
  unfold transf_clight_program_opt in TRANSF. clarify.

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
  unfold transf_cminor_program_opt in TRANSF. clarify.

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
  exploit rtl_exists_forward_simulation; eauto. intros [prtl1 [rtlprog1 [Hrtlprogsim1 [Hrtlprog1 TRANSF1]]]].
  unfold transf_rtl_program_to_asm_opt in TRANSF1. clarify.

  eapply Tree.Forall2_reduce in T5; eauto;
    [|eapply (transform_partial_program2_link_program Language.Language_RTL Language.Language_LTL)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply Allocation_sig].
  destruct T5 as [ltlprog0 [Hltlprog0 Hltlsim0]].
  apply Allocproof.transf_program_correct in Hltlsim0.

  eapply Tree.Forall2_reduce in T3; eauto;
    [|eapply (transform_program_link_program); auto].
  destruct T3 as [ltlprog1 [Hltlprog1 Hltlsim1]]. subst.
  generalize (Tunnelingproof.transf_program_correct ltlprog0) as Hltlsim1. intro.

  eapply Tree.Forall2_reduce in T2; eauto;
    [|eapply (transform_partial_program2_link_program Language.Language_LTL Language.Language_Linear)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply Linearize_sig].
  destruct T2 as [linearprog0 [Hlinearprog0 Hlinearsim0]].
  apply Linearizeproof.transf_program_correct in Hlinearsim0.

  eapply Tree.Forall2_reduce in T1; eauto;
    [|eapply (transform_program_link_program); auto].
  destruct T1 as [linearprog1 [Hlinearprog1 Hlinearsim1]]. subst.
  generalize (CleanupLabelsproof.transf_program_correct linearprog0) as Hlinearsim1. intro.

  eapply Tree.Forall2_reduce in T0; eauto;
    [|eapply (transform_partial_program2_link_program Language.Language_Linear Language.Language_Mach)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply Stacking_sig].
  destruct T0 as [machprog [Hmachprog Hmachsim]].
  eapply Stackingproof.transf_program_correct in Hmachsim; eauto;
    [|eexact Asmgenproof.return_address_exists; eassumption].

  apply asmtree_drop_flag in TRANSF1. destruct TRANSF1 as [asmtree0 [TRANSF1 TEQ]].

  eapply Tree.Forall2_reduce in TRANSF1; eauto;
    [|eapply (transform_partial_program2_link_program Language.Language_Mach Language.Language_Asm)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply Asmgen_sig].
  destruct TRANSF1 as [asmprog [Hasmprog Hasmsim]].
  eapply Asmgenproof.transf_program_correct in Hasmsim; eauto.

  (* epilogue *)
  exists asmprog. eexists.
  repeat (auto; try (eapply compose_forward_simulation; [|eauto; fail])).
  rewrite TEQ. eauto.
Qed.

Lemma linker_correct_determinate_optd
        ctree asmtree cprog
        (CLINK: Tree.reduce (link_program Language.Language_C) ctree = Some cprog)
        (TRANSF: Tree.Forall2 (fun s t => transf_c_program_opt (fst t) s = OK (snd t)) ctree asmtree):
  exists (asmprog:Asm.program)
    (_:backward_simulation (atomic (Cstrategy.semantics cprog)) (Asm.semantics asmprog)),
    Tree.reduce (link_program Language.Language_Asm) (Tree.map snd asmtree) = Some asmprog.
Proof.
  exploit linker_correct_determinate_forward_optd; eauto.
  intros [asmprog [Hsim Hasmprog]]. exists asmprog.
  eexists; auto.
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces. eapply Asm.semantics_determinate.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem linker_correct_optd
        ctree asmtree cprog
        (CLINK: Tree.reduce (link_program Language.Language_C) ctree = Some cprog)
        (TRANSF: Tree.Forall2 (fun s t => transf_c_program_opt (fst t) s = OK (snd t)) ctree asmtree):
  exists (asmprog:Asm.program)
    (_:backward_simulation (Csem.semantics cprog) (Asm.semantics asmprog)),
    Tree.reduce (link_program Language.Language_Asm) (Tree.map snd asmtree) = Some asmprog.
Proof.
  exploit linker_correct_determinate_optd; eauto.
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
