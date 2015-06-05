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

Lemma SimplExpr_sepcomp_rel
      cprog clightprog
      (Htrans: SimplExpr.transl_program cprog = OK clightprog):
  @sepcomp_rel
    Language_C Language_Clight
    (fun _ f tf => SimplExprspec.tr_function f tf)
    (fun _ ef tef => ef = tef) (@OK _)
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
    (fun p f tf =>
       exists hf,
         SelectLongproof.i64_helpers_correct (Genv.globalenv p) hf /\
         Selection.sel_function hf (Genv.globalenv p) f = OK tf)
    (fun p ef tef =>
       exists hf,
         SelectLongproof.i64_helpers_correct (Genv.globalenv p) hf /\
         ef = tef)
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
        exists x. split; auto. apply Selectionproof.get_helpers_correct. auto.
      * eapply (@grel_ef Language_Cminor Language_CminorSel); simpl; auto.
        exists x. split; auto. apply Selectionproof.get_helpers_correct. auto.
    + apply IHdefs; auto.
  - monadInv Hdefs. constructor; simpl.
    + split; auto. eexists. split; [reflexivity|].
      eapply (@grel_gv Language_Cminor Language_CminorSel); auto.
    + apply IHdefs; auto.
Qed.

Lemma Tailcall_sepcomp_rel
      rtlprog1 rtlprog2
      (Htrans: Tailcall.transf_program rtlprog1 = rtlprog2 \/ rtlprog1 = rtlprog2):
  @sepcomp_rel
    Language_RTL Language_RTL
    (fun p f tf => Tailcall.transf_function f = tf \/ f = tf)
    (fun p ef tef => ef = tef)
    (@OK _)
    rtlprog1 rtlprog2.
Proof.
  inv Htrans.
  - apply transf_program_sepcomp_rel'.
    unfold Tailcall.transf_program. f_equal.
    apply Axioms.functional_extensionality. intro fd.
    destruct fd; auto.
  - apply transf_program_sepcomp_rel'_identical; auto.
Qed.

Lemma Inlining_sepcomp_rel
      rtlprog1 rtlprog2
      (Htrans: Inlining.transf_program rtlprog1 = OK rtlprog2 \/ rtlprog1 = rtlprog2):
  @sepcomp_rel
    Language_RTL Language_RTL
    (fun p f tf => Inlining.transf_function (Inlining.funenv_program p) f = OK tf \/ f = tf)
    (fun p ef tef => (fun _ ef => OK ef) p ef = OK tef)
    (@OK _)
    rtlprog1 rtlprog2.
Proof.
  inv Htrans.
  - apply transf_partial_sepcomp_rel'.
    unfold progT, RTL.program, RTL.fundef in *. simpl in *. rewrite <- H.
    unfold Inlining.transf_program. f_equal.
    apply Axioms.functional_extensionality. intro fd.
    destruct fd; auto.
  - apply transf_partial_sepcomp_rel'_identical; auto.
Qed.

Lemma Renumber_sepcomp_rel
      rtlprog1 rtlprog2
      (Htrans: Renumber.transf_program rtlprog1 = rtlprog2 \/ rtlprog1 = rtlprog2):
  @sepcomp_rel
    Language_RTL Language_RTL
    (fun p f tf => Renumber.transf_function f = tf \/ f = tf)
    (fun p ef tef => ef = tef)
    (@OK _)
    rtlprog1 rtlprog2.
Proof.
  inv Htrans.
  - apply transf_program_sepcomp_rel'.
    unfold Renumber.transf_program. f_equal.
    apply Axioms.functional_extensionality. intro fd.
    destruct fd; auto.
  - apply transf_program_sepcomp_rel'_identical. auto.
Qed.

Lemma Constprop_sepcomp_rel
      rtlprog1 rtlprog2
      (Htrans: Constprop.transf_program rtlprog1 = rtlprog2 \/ rtlprog1 = rtlprog2):
  @sepcomp_rel
    Language_RTL Language_RTL
    (fun p f tf => Constprop.transf_function (ValueAnalysis.romem_for_program p) f = tf \/ f = tf)
    (fun p ef tef => ef = tef)
    (@OK _)
    rtlprog1 rtlprog2.
Proof.
  inv Htrans.
  - apply transf_program_sepcomp_rel'.
    unfold Constprop.transf_program. f_equal.
    apply Axioms.functional_extensionality. intro fd.
    destruct fd; auto.
  - apply transf_program_sepcomp_rel'_identical. auto.
Qed.

Lemma CSE_sepcomp_rel
      rtlprog1 rtlprog2
      (Htrans: CSE.transf_program rtlprog1 = OK rtlprog2 \/ rtlprog1 = rtlprog2):
  @sepcomp_rel
    Language_RTL Language_RTL
    (fun p f tf => CSE.transf_function (ValueAnalysis.romem_for_program p) f = OK tf \/ f = tf)
    (fun p ef tef => (fun _ ef => OK ef) p ef = OK tef)
    (@OK _)
    rtlprog1 rtlprog2.
Proof.
  inv Htrans.
  - apply transf_partial_sepcomp_rel'.
    unfold progT, RTL.program, RTL.fundef in *. simpl in *. rewrite <- H.
    unfold CSE.transf_program. f_equal.
    apply Axioms.functional_extensionality. intro fd.
    destruct fd; auto.
  - apply transf_partial_sepcomp_rel'_identical. auto.
Qed.

Lemma Deadcode_sepcomp_rel
      rtlprog1 rtlprog2
      (Htrans: Deadcode.transf_program rtlprog1 = OK rtlprog2 \/ rtlprog1 = rtlprog2):
  @sepcomp_rel
    Language_RTL Language_RTL
    (fun p f tf => Deadcode.transf_function (ValueAnalysis.romem_for_program p) f = OK tf \/ f = tf)
    (fun p ef tef => (fun _ ef => OK ef) p ef = OK tef)
    (@OK _)
    rtlprog1 rtlprog2.
Proof.
  inv Htrans.
  - apply transf_partial_sepcomp_rel'.
    unfold progT, RTL.program, RTL.fundef in *. simpl in *. rewrite <- H.
    unfold Deadcode.transf_program. f_equal.
    apply Axioms.functional_extensionality. intro fd.
    destruct fd; auto.
  - apply transf_partial_sepcomp_rel'_identical. auto.
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
           | [H: exists (_:SelectLong.helper_functions), _ |- _] => destruct H
           | [H: _ /\ _ |- _] => destruct H
         end;
  subst; auto.

Definition transf_rtl_program_to_asm (f: RTL.program) : res Asm.program :=
   OK f
   @@ print (print_RTL 0)
   @@@ time "Register allocation" Allocation.transf_program
   @@ print print_LTL
   @@ time "Branch tunneling" Tunneling.tunnel_program
  @@@ Linearize.transf_program
   @@ time "Label cleanup" CleanupLabels.transf_program
  @@@ time "Mach generation" Stacking.transf_program
   @@ print print_Mach
  @@@ time "Asm generation" Asmgen.transf_program.

Definition transf_cminor_program_to_rtl (p: Cminor.program) : res RTL.program :=
   OK p
   @@ print print_Cminor
  @@@ time "Instruction selection" Selection.sel_program
  @@@ time "RTL generation" RTLgen.transl_program.

Definition transf_clight_program_to_rtl (p: Clight.program) : res RTL.program :=
  OK p 
   @@ print print_Clight
  @@@ time "Simplification of locals" SimplLocals.transf_program
  @@@ time "C#minor generation" Cshmgen.transl_program
  @@@ time "Cminor generation" Cminorgen.transl_program
  @@@ transf_cminor_program_to_rtl.

Definition transf_c_program_to_rtl (p: Csyntax.program) : res RTL.program :=
  OK p 
  @@@ time "Clight generation" SimplExpr.transl_program
  @@@ transf_clight_program_to_rtl.

Lemma Tree_Forall2_split2:
  forall (A B C : Type) (pred1 : A -> B -> Prop) (predb : B -> B -> Prop)
         (pred2 : B -> C -> Prop) (treeA : Tree.t A) (treeC : Tree.t C),
    Tree.Forall2
      (fun (a : A) (c : C) => exists (b1 b2:B), pred1 a b1 /\ (predb b1 b2 /\ pred2 b2 c)) treeA treeC <->
    (exists (treeB1 treeB2: Tree.t B),
       Tree.Forall2 pred1 treeA treeB1 /\ Tree.Forall2 predb treeB1 treeB2 /\ Tree.Forall2 pred2 treeB2 treeC).
Proof.
  intros.
  remember (fun a c => exists b1 b2, pred1 a b1 /\ predb b1 b2 /\ pred2 b2 c) as predA.
  remember (fun a c => exists b1, pred1 a b1 /\ exists b2, predb b1 b2 /\ pred2 b2 c) as predB.
  assert (pcomp: Tree.Forall2 predA treeA treeC <-> Tree.Forall2 predB treeA treeC).
  { apply Tree.Forall2_compat. subst. split; intros; des; eauto. }
  subst. rewrite -> pcomp.
  generalize (Tree.Forall2_split pred1 (fun b c => exists b2, predb b b2 /\ pred2 b2 c) treeA treeC). intros. rewrite -> H.
  split; intros; des.
  - apply Tree.Forall2_split in H1. des. eauto.
  - exists treeB1. split; auto. apply Tree.Forall2_split. eauto.
Qed.

Inductive rtl_optimized_1: forall (rtl: RTL.program) (ortl: RTL.program), Prop :=
| rtlopt_tailcall: forall r1,
                     rtl_optimized_1 r1 (Tailcall.transf_program r1)
| rtlopt_inlining: forall r1 r1' (TR_OK: Inlining.transf_program r1 = OK r1'),
                     rtl_optimized_1 r1 r1'
| rtlopt_renumber: forall r1,
                     rtl_optimized_1 r1 (Renumber.transf_program r1)
| rtlopt_constprop: forall r1,
                      rtl_optimized_1 r1 (Constprop.transf_program r1)
| rtlopt_cse: forall r1 r1' (TR_OK: CSE.transf_program r1 = OK r1'),
                rtl_optimized_1 r1 r1'
| rtlopt_deadcode: forall r1 r1' (TR_OK: Deadcode.transf_program r1 = OK r1'),
                     rtl_optimized_1 r1 r1'.

Inductive rtl_optimized: forall (rtl: RTL.program) (ortl: RTL.program), Prop :=
| rtlopt_none: forall r, rtl_optimized r r
| rtlopt_some: forall r1 r2 r2' (ROPT: rtl_optimized r1 r2) (ROPT1: rtl_optimized_1 r2 r2'),
                 rtl_optimized r1 r2'.

Inductive rtl_opt1_tree: forall (tr: Tree.t RTL.program) (tr': Tree.t RTL.program), Prop :=
| rtl_opt1_tree_base: forall r r' (ROPT: rtl_optimized_1 r r'),
                        rtl_opt1_tree (Tree.Tree_singleton r) (Tree.Tree_singleton r')
| rtl_opt1_tree_comp_left: forall r r' tr (ROPTT: rtl_opt1_tree r r'),
                             rtl_opt1_tree (Tree.Tree_composite r tr) (Tree.Tree_composite r' tr)
| rtl_opt1_tree_comp_right: forall r r' tr (ROPTT: rtl_opt1_tree r r'),
                              rtl_opt1_tree (Tree.Tree_composite tr r) (Tree.Tree_composite tr r').

Inductive rtl_opt_tree: forall (tr: Tree.t RTL.program) (tr': Tree.t RTL.program), Prop :=
| rtl_opt_tree_id: forall tr, rtl_opt_tree tr tr
| rtl_opt_tree_opt: forall tr tr' tr'' (ROPTT: rtl_opt_tree tr tr') (ROPT1T: rtl_opt1_tree tr' tr''),
                      rtl_opt_tree tr tr''.

Lemma rtl_opt_tree_attach_left:
  forall tr tr' tr2 (ROPTT: rtl_opt_tree tr tr'),
    rtl_opt_tree (Tree.Tree_composite tr tr2) (Tree.Tree_composite tr' tr2).
Proof.
  intros. revert tr2.
  induction ROPTT; intros; econstructor.
  - apply IHROPTT.
  - constructor. auto.
Qed.

Lemma rtl_opt_tree_attach_right:
  forall tr tr' tr2 (ROPTT: rtl_opt_tree tr tr'),
    rtl_opt_tree (Tree.Tree_composite tr2 tr) (Tree.Tree_composite tr2 tr').
Proof.
  intros. revert tr2.
  induction ROPTT; intros; econstructor.
  - apply IHROPTT.
  - constructor. auto.
Qed.

Lemma rtl_opt_tree_trans:
  forall tr1 tr2 tr3
         (ROPTT1: rtl_opt_tree tr1 tr2)
         (ROPTT2: rtl_opt_tree tr2 tr3),
    rtl_opt_tree tr1 tr3.
Proof.
  intros. generalize dependent tr1.
  induction ROPTT2; intros; try auto.
  econstructor;auto.
Qed.

Lemma Tree_Forall2_opt_rtl_opt_tree:
  forall (tr1 tr2: Tree.t RTL.program)
         (ROPTT: Tree.Forall2 rtl_optimized tr1 tr2),
    rtl_opt_tree tr1 tr2.
Proof.
  intros.
  induction ROPTT.
  - induction Hpred.
    * constructor.
    * eapply rtl_opt_tree_trans. eauto.
      econstructor; constructor; auto.
  - eapply rtl_opt_tree_trans.
    + eapply rtl_opt_tree_attach_left. eauto.
    + eapply rtl_opt_tree_attach_right. eauto.
Qed.

Lemma Tree_Forall2_eq_same:
  forall X (tr: Tree.t X), Tree.Forall2 eq tr tr.
Proof.
  intros. induction tr; constructor; auto.
Qed.

Lemma rtl_opt1_tree_destruct:
  forall tr tr' (ROPT1T: rtl_opt1_tree tr tr'),
    << TAILCALL: Tree.Forall2 (fun p1 p2 => (Tailcall.transf_program p1 = p2) \/ p1 = p2) tr tr' >>
    \/  << INLINING: Tree.Forall2 (fun p1 p2 => (Inlining.transf_program p1 = OK p2) \/ p1 = p2) tr tr' >>
    \/  << RENUMBER: Tree.Forall2 (fun p1 p2 => (Renumber.transf_program p1 = p2) \/ p1 = p2) tr tr' >>
    \/  << CONSTPROP: Tree.Forall2 (fun p1 p2 => (Constprop.transf_program p1 = p2) \/ p1 = p2) tr tr' >>
    \/  << CSE: Tree.Forall2 (fun p1 p2 => (CSE.transf_program p1 = OK p2) \/ p1 = p2) tr tr' >>
    \/  << DEADCODE: Tree.Forall2 (fun p1 p2 => (Deadcode.transf_program p1 = OK p2) \/ p1 = p2) tr tr' >>.
Proof.
  intros. induction ROPT1T.
  - inv ROPT; [|right|right;right|right;right;right|right;right;right;right |right;right;right;right;right ]; [left|left|left|left|left| ]; constructor; auto.
  - des; [|right|right;right|right;right;right|right;right;right;right |right;right;right;right;right ]; [left|left|left|left|left|];
    (constructor; auto; eapply Tree.Forall2_implies;
    [ intros; right; apply H | apply Tree_Forall2_eq_same]).
  - des; [|right|right;right|right;right;right|right;right;right;right |right;right;right;right;right ]; [left|left|left|left|left|];
    (constructor; auto; eapply Tree.Forall2_implies;
    [ intros; right; apply H | apply Tree_Forall2_eq_same]).
Qed.

Lemma rtl_opt1_tree_reduce_simulation:
  forall tr tr' rtlprog
         (ROPT1T: rtl_opt1_tree tr tr')
         (REDUCE: Tree.reduce (link_program Language_RTL) tr = Some rtlprog),
  exists rtlprog'
    (Hrtlsim': forward_simulation (RTL.semantics rtlprog) (RTL.semantics rtlprog')),
    << Hrtlprog': Tree.reduce (link_program Language_RTL) tr' = Some rtlprog' >>.
Proof.
  intros.
  apply rtl_opt1_tree_destruct in ROPT1T. des.
  - eapply Tree.Forall2_implies in TAILCALL; [|apply Tailcall_sepcomp_rel].
    eapply Tree.Forall2_reduce in TAILCALL; eauto; [|eapply (@link_program_sepcomp_rel Language_RTL Language_RTL id)]; simplify.
    + destruct TAILCALL as [rtlprog1 [Hrtlprog1 Hrtlsim1]].
      apply Tailcallproof_sepcomp.transf_program_correct in Hrtlsim1. eexists. eauto.
    + des; subst; [apply Tailcall_sig | auto].
  - eapply Tree.Forall2_implies in INLINING; [|apply Inlining_sepcomp_rel].
    eapply Tree.Forall2_reduce in INLINING; eauto; [|eapply (@link_program_sepcomp_rel Language_RTL Language_RTL id)]; simplify.
    + destruct INLINING as [rtlprog1 [Hrtlprog1 Hrtlsim1]].
      apply Inliningproof_sepcomp.transf_program_correct in Hrtlsim1. eexists. eauto.
    + des; subst; [eapply Inlining_sig|]; eauto.
  - eapply Tree.Forall2_implies in RENUMBER; [|apply Renumber_sepcomp_rel].
    eapply Tree.Forall2_reduce in RENUMBER; eauto; [|eapply (@link_program_sepcomp_rel Language_RTL Language_RTL id)]; simplify.
    + destruct RENUMBER as [rtlprog1 [Hrtlprog1 Hrtlsim1]].
      apply Renumberproof_sepcomp.transf_program_correct in Hrtlsim1. eexists. eauto.
    + des; subst; auto.
  - eapply Tree.Forall2_implies in CONSTPROP; [|apply Constprop_sepcomp_rel].
    eapply Tree.Forall2_reduce in CONSTPROP; eauto; [|eapply (@link_program_sepcomp_rel Language_RTL Language_RTL id)]; simplify.
    + destruct CONSTPROP as [rtlprog1 [Hrtlprog1 Hrtlsim1]].
      apply Constpropproof_sepcomp.transf_program_correct in Hrtlsim1. eexists. eauto.
    + des; subst; auto.
  - eapply Tree.Forall2_implies in CSE; [|apply CSE_sepcomp_rel].
    eapply Tree.Forall2_reduce in CSE; eauto; [|eapply (@link_program_sepcomp_rel Language_RTL Language_RTL id)]; simplify.
    + destruct CSE as [rtlprog1 [Hrtlprog1 Hrtlsim1]].
      apply CSEproof_sepcomp.transf_program_correct in Hrtlsim1. eexists. eauto.
    + des; subst; [eapply CSE_sig|]; eauto.
  - eapply Tree.Forall2_implies in DEADCODE; [|apply Deadcode_sepcomp_rel].
    eapply Tree.Forall2_reduce in DEADCODE; eauto; [|eapply (@link_program_sepcomp_rel Language_RTL Language_RTL id)]; simplify.
    + destruct DEADCODE as [rtlprog1 [Hrtlprog1 Hrtlsim1]].
      apply Deadcodeproof_sepcomp.transf_program_correct in Hrtlsim1. eexists. eauto.
    + des; subst; [eapply Deadcode_sig|]; eauto.
Qed.

Inductive match_state_refl: forall (s1 s2:RTL.state), Prop :=
| match_state_refl_intro: forall s, match_state_refl s s.

Lemma forward_simulation_rtl_refl:
  forall prog, forward_simulation (RTL.semantics prog) (RTL.semantics prog).
Proof.
  intros.
  eapply forward_simulation_step; eauto; intros.
  - eexists. split; eauto. apply (match_state_refl_intro s1).
  - inv H; auto.
  - eexists. inv H0. split; eauto. constructor.
Qed.

Lemma rtl_optimized_reduce_simulation:
  forall (rtlprog: RTL.program)
         (tr1 tr2: Tree.t RTL.program)
         (REDUCE: Tree.reduce (link_program Language_RTL) tr1 = Some rtlprog)
         (OPT: rtl_opt_tree tr1 tr2),
  exists rtlprog'
         (Hrtlsim': forward_simulation (RTL.semantics rtlprog) (RTL.semantics rtlprog')),
    << Hrtlprog': Tree.reduce (link_program Language_RTL) tr2 = Some rtlprog' >>.
Proof.
  intros. generalize dependent rtlprog.
  induction OPT; intros.
  - exists rtlprog. exists (forward_simulation_rtl_refl rtlprog); eauto.
  - exploit IHOPT; eauto. intros. des.
    exploit rtl_opt1_tree_reduce_simulation; eauto. intros. des.
    exists rtlprog'0.
    exists (compose_forward_simulation Hrtlsim' Hrtlsim'0); eauto.
Qed.

Definition compiled (c: Csyntax.program) (a:Asm.program) : Prop :=
  exists rtl ortl,
    transf_c_program_to_rtl c = OK rtl
    /\ rtl_optimized rtl ortl
    /\ transf_rtl_program_to_asm ortl = OK a.

Theorem linker_correct
        ctree asmtree cprog
        (CLINK: Tree.reduce (link_program Language_C) ctree = Some cprog)
        (TRANSF: Tree.Forall2 (fun c a => compiled c a) ctree asmtree):
  exists (asmprog:Asm.program)
    (_:forward_simulation (Cstrategy.semantics cprog) (Asm.semantics asmprog)),
    Tree.reduce (link_program Language_Asm) asmtree = Some asmprog.
Proof.
  repeat intro.

  (* C *)
  unfold compiled in TRANSF.
  eapply Tree_Forall2_split2 in TRANSF. des.

  unfold transf_c_program_to_rtl in TRANSF. clarify.
  eapply Tree.Forall2_implies in T; [|apply SimplExpr_sepcomp_rel].
  eapply Tree.Forall2_reduce in T; eauto;
    [|eapply (@link_program_sepcomp_rel Language_C Language_Clight id)]; simplify;
    [|apply SimplExpr_sig; auto].
  destruct T as [clightprog [Hclightprog Hclightsim]].
  apply SimplExprproof_sepcomp.transl_program_correct in Hclightsim.

  (* Clight *)
  unfold transf_clight_program_to_rtl in TRANSF. clarify.

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
  unfold transf_cminor_program_to_rtl in TRANSF. clarify.

  eapply Tree.Forall2_implies in T; [|apply Selection_sepcomp_rel].
  eapply Tree.Forall2_reduce in T; eauto;
    [|eapply (@link_program_sepcomp_rel Language_Cminor Language_CminorSel id)]; simplify;
    [|eapply Selection_sig; eauto
     |eexists; split; auto; eapply Selectionproof_sepcomp.Hget_helpers_monotone; eauto].

  destruct T as [cminorselprog [Hcminorselprog Hcminorselsim]].
  apply Selectionproof_sepcomp.transl_program_correct in Hcminorselsim.

  eapply Tree.Forall2_reduce in TRANSF; eauto;
    [|eapply (transform_partial_program2_link_program Language_CminorSel Language_RTL)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply RTLgen_sig].
  destruct TRANSF as [rtlprog0 [Hrtlprog0 Hrtlsim0]].
  apply RTLgenproof.transf_program_correct in Hrtlsim0.

(* RTL *)
  exploit rtl_optimized_reduce_simulation; eauto.
  apply Tree_Forall2_opt_rtl_opt_tree. eauto.
  intros. des.
  unfold transf_rtl_program_to_asm in TRANSF1. clarify.

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

  eapply Tree.Forall2_reduce in TRANSF1; eauto;
    [|eapply (transform_partial_program2_link_program Language_Mach Language_Asm)];
    [|apply globfun_linkable_transf_partial_fundef];
    [|apply Asmgen_sig].
  destruct TRANSF1 as [asmprog [Hasmprog Hasmsim]].
  eapply Asmgenproof.transf_program_correct in Hasmsim; eauto.

  (* epilogue *)
  exists asmprog. eexists; auto.
  repeat (auto; try (eapply compose_forward_simulation; [|eauto; fail])).
Qed.
