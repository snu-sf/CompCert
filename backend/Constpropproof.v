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

(** Correctness proof for constant propagation. *)

Require Import Coqlib.
Require Import Maps.
Require Compopts.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Lattice.
Require Import Kildall.
Require Import ValueDomain.
Require Import ValueAOp.
Require Import ValueAnalysis.
Require Import ConstpropOp.
Require Import Constprop.
Require Import ConstpropOpproof.
(* new *) Require Import Language.
(* new *) Require Import Linksub.
(* new *) Require Import SepcompRel.
(* new *) Require Import RTLExtra.
(* new *) Require Import sflib.

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
(* new *) Hypothesis TRANSF:
(* new *)   @sepcomp_rel
(* new *)     Language_RTL Language_RTL
(* new *)     (fun p f tf => transf_function (romem_for_program p) f = tf \/ f = tf)
(* new *)     (fun p ef tef => ef = tef)
(* new *)     (@Errors.OK _)
(* new *)     prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Let rm := romem_for_program prog.

(* new *) Inductive match_fundef prog: forall (fd fd':fundef), Prop :=
(* new *) | match_fundef_transl fd fd' sprog
(* new *)     (SPROG: program_linksub Language_RTL sprog prog)
(* new *)     (FUN: transf_fundef (romem_for_program sprog) fd = fd'):
(* new *)     match_fundef prog fd fd'
(* new *) | match_fundef_identical fd:
(* new *)     match_fundef prog fd fd.

(** * Correctness of the code transformation *)

(** We now show that the transformed code after constant propagation
  has the same semantics as the original code. *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  apply (find_symbol_transf_optionally _ _ TRANSF).
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  apply (find_var_info_transf_optionally _ _ TRANSF).
Qed.

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\
             match_fundef prog f tf.
Proof.  
  intros.
  exploit (find_funct_transf_optionally _ _ TRANSF); eauto. simpl in *.
  intros [tf [Htf [[sprog [Hsprog Hf]]|Hf]]].
  eexists. split; eauto.
  destruct f; auto.
  econstructor; eauto.
  subst. constructor.
  subst. eexists. split; eauto. constructor.
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
    Genv.find_funct_ptr tge b = Some tf /\
    match_fundef prog f tf.
Proof.  
  intros. 
  exploit (find_funct_ptr_transf_optionally _ _ TRANSF); eauto. simpl in *.
  intros [tf [Htf [[sprog [Hsprog Hf]]|Hf]]].
  eexists. split; eauto.
  destruct f; auto.
  subst. econstructor; eauto.
  subst. constructor.
  subst. eexists. split; eauto. constructor.
Qed.

Lemma sig_function_translated:
  forall rm f,
  funsig (transf_fundef rm f) = funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

Lemma match_fundef_sig:
  forall f1 f2 sprog (MATCHFD: match_fundef sprog f1 f2), funsig f2 = funsig f1.
Proof.
  intros. inv MATCHFD; auto.
  eapply sig_function_translated; eauto.
Qed.

Definition regs_lessdef (rs1 rs2: regset) : Prop :=
  forall r, Val.lessdef (rs1#r) (rs2#r).

Lemma regs_lessdef_regs:
  forall rs1 rs2, regs_lessdef rs1 rs2 ->
  forall rl, Val.lessdef_list rs1##rl rs2##rl.
Proof.
  induction rl; constructor; auto.
Qed.

Lemma set_reg_lessdef:
  forall r v1 v2 rs1 rs2,
  Val.lessdef v1 v2 -> regs_lessdef rs1 rs2 -> regs_lessdef (rs1#r <- v1) (rs2#r <- v2).
Proof.
  intros; red; intros. repeat rewrite Regmap.gsspec. 
  destruct (peq r0 r); auto.
Qed.

Lemma init_regs_lessdef:
  forall rl vl1 vl2,
  Val.lessdef_list vl1 vl2 ->
  regs_lessdef (init_regs vl1 rl) (init_regs vl2 rl).
Proof.
  induction rl; simpl; intros.
  red; intros. rewrite Regmap.gi. auto.
  inv H. red; intros. rewrite Regmap.gi. auto.
  apply set_reg_lessdef; auto.
Qed.

Lemma find_function_translated:
  forall ros rs fd trs,
  find_function ge ros rs = Some fd ->
  regset_lessdef rs trs ->
  exists tfd, find_function tge ros trs = Some tfd /\ 
              match_fundef prog fd tfd.
Proof.
  intros. destruct ros as [r|id]; simpl in *.
- assert (LD: Val.lessdef rs#r trs#r) by eauto. inv LD.
  apply functions_translated; auto.
  rewrite <- H2 in H; discriminate.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try discriminate.
  apply function_ptr_translated; auto.
Qed.

Lemma transf_ros_correct:
  forall bc rs ae ros f rs',
  genv_match bc ge ->
  ematch bc rs ae ->
  find_function ge ros rs = Some f ->
  regs_lessdef rs rs' ->
  exists tf,
    find_function tge (transf_ros ae ros) rs' = Some tf /\
    match_fundef prog f tf.
Proof.
  intros until rs'; intros GE EM FF RLD. destruct ros; simpl in *.
- (* function pointer *)
  generalize (EM r); fold (areg ae r); intro VM. generalize (RLD r); intro LD.
  assert (DEFAULT: exists tf, find_function tge (inl _ r) rs' = Some tf /\ match_fundef prog f tf).
  {
    simpl. inv LD. apply functions_translated; auto. rewrite <- H0 in FF; discriminate. 
  }
  destruct (areg ae r); auto. destruct p; auto. 
  predSpec Int.eq Int.eq_spec ofs Int.zero; intros; auto. 
  subst ofs. exploit vmatch_ptr_gl; eauto. intros LD'. inv LD'; try discriminate.
  rewrite H1 in FF. unfold Genv.symbol_address in FF. 
  simpl. rewrite symbols_preserved.
  destruct (Genv.find_symbol ge id) as [b|]; try discriminate.
  simpl in FF. rewrite dec_eq_true in FF.
  apply function_ptr_translated; auto.
  rewrite <- H0 in FF; discriminate.
- (* function symbol *)
  rewrite symbols_preserved. 
  destruct (Genv.find_symbol ge i) as [b|]; try discriminate.
  apply function_ptr_translated; auto.
Qed.

Lemma const_for_result_correct:
  forall a op bc v sp m,
  const_for_result a = Some op ->
  vmatch bc v a ->
  bc sp = BCstack ->
  genv_match bc ge ->
  exists v', eval_operation tge (Vptr sp Int.zero) op nil m = Some v' /\ Val.lessdef v v'.
Proof.
  unfold const_for_result; intros.
  destruct a; try discriminate.
- (* integer *)
  inv H. inv H0. exists (Vint n); auto.
- (* float *)
  destruct (Compopts.generate_float_constants tt); inv H. inv H0. exists (Vfloat f); auto.
- (* single *)
  destruct (Compopts.generate_float_constants tt); inv H. inv H0. exists (Vsingle f); auto.
- (* pointer *)
  destruct p; try discriminate.
  + (* global *)
    inv H. exists (Genv.symbol_address ge id ofs); split.
    unfold Genv.symbol_address. rewrite <- symbols_preserved. reflexivity.
    eapply vmatch_ptr_gl; eauto. 
  + (* stack *)
    inv H. exists (Vptr sp ofs); split. 
    simpl; rewrite Int.add_zero_l; auto. 
    eapply vmatch_ptr_stk; eauto. 
Qed.

Inductive match_pc (f: function) (ae: AE.t): nat -> node -> node -> Prop :=
  | match_pc_base: forall n pc,
      match_pc f ae n pc pc
  | match_pc_nop: forall n pc s pcx,
      f.(fn_code)!pc = Some (Inop s) ->
      match_pc f ae n s pcx ->
      match_pc f ae (S n) pc pcx
  | match_pc_cond: forall n pc cond args s1 s2 b pcx,
      f.(fn_code)!pc = Some (Icond cond args s1 s2) ->
      resolve_branch (eval_static_condition cond (aregs ae args)) = Some b ->
      match_pc f ae n (if b then s1 else s2) pcx ->
      match_pc f ae (S n) pc pcx.

Lemma match_successor_rec:
  forall f ae n pc, match_pc f ae n pc (successor_rec n f ae pc).
Proof.
  induction n; simpl; intros.
- apply match_pc_base.
- destruct (fn_code f)!pc as [[]|] eqn:INSTR; try apply match_pc_base.
  eapply match_pc_nop; eauto.
  destruct (resolve_branch (eval_static_condition c (aregs ae l))) as [b|] eqn:COND.
  eapply match_pc_cond; eauto.
  apply match_pc_base.
Qed.

Lemma match_successor:
  forall f ae pc, match_pc f ae num_iter pc (successor f ae pc).
Proof.
  unfold successor; intros. apply match_successor_rec.
Qed.

Section BUILTIN_STRENGTH_REDUCTION.

Variable bc: block_classification.
Hypothesis GE: genv_match bc ge.
Variable ae: AE.t.
Variable rs: regset.
Hypothesis MATCH: ematch bc rs ae.

Lemma annot_strength_reduction_correct:
  forall targs args targs' args' eargs,
  annot_strength_reduction ae targs args = (targs', args') ->
  eventval_list_match ge eargs (annot_args_typ targs) rs##args ->
  exists eargs',
  eventval_list_match ge eargs' (annot_args_typ targs') rs##args'
  /\ annot_eventvals targs' eargs' = annot_eventvals targs eargs.
Proof.
  induction targs; simpl; intros.
- inv H. simpl. exists eargs; auto. 
- destruct a.
  + destruct args as [ | arg args0]; simpl in H0; inv H0.
    destruct (annot_strength_reduction ae targs args0) as [targs'' args''] eqn:E.
    exploit IHtargs; eauto. intros [eargs'' [A B]].
    assert (DFL:
      exists eargs',
      eventval_list_match ge eargs' (annot_args_typ (AA_arg ty :: targs'')) rs##(arg :: args'')
      /\ annot_eventvals (AA_arg ty :: targs'') eargs' = ev1 :: annot_eventvals targs evl).
    {
      exists (ev1 :: eargs''); split.
      simpl; constructor; auto. simpl. congruence.
    }
    destruct ty; destruct (areg ae arg) as [] eqn:E2; inv H; auto.
    * exists eargs''; split; auto; simpl; f_equal; auto. 
      generalize (MATCH arg); fold (areg ae arg); rewrite E2; intros VM.
      inv VM. rewrite <- H0 in *. inv H5; auto.
    * destruct (Compopts.generate_float_constants tt); inv H1; auto. 
      exists eargs''; split; auto; simpl; f_equal; auto. 
      generalize (MATCH arg); fold (areg ae arg); rewrite E2; intros VM.
      inv VM. rewrite <- H0 in *. inv H5; auto.
  + destruct (annot_strength_reduction ae targs args) as [targs'' args''] eqn:E.
    inv H.
    exploit IHtargs; eauto. intros [eargs'' [A B]].
    exists eargs''; simpl; split; auto. congruence.
  + destruct (annot_strength_reduction ae targs args) as [targs'' args''] eqn:E.
    inv H.
    exploit IHtargs; eauto. intros [eargs'' [A B]].
    exists eargs''; simpl; split; auto. congruence.
Qed.

Lemma vmatch_ptr_gl':
  forall v id ofs,
  vmatch bc v (Ptr (Gl id ofs)) ->
  v = Vundef \/ exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b ofs.
Proof.
  intros. inv H; auto. inv H2. right; exists b; split; auto. eapply GE; eauto.
Qed. 

Lemma builtin_strength_reduction_correct:
  forall ef args m t vres m',
  external_call ef ge rs##args m t vres m' ->
  let (ef', args') := builtin_strength_reduction ae ef args in
  external_call ef' ge rs##args' m t vres m'.
Proof.
  intros until m'. functional induction (builtin_strength_reduction ae ef args); intros; auto.
+ simpl in H. assert (V: vmatch bc (rs#r1) (Ptr (Gl symb n1))) by (rewrite <- e1; apply MATCH). 
  exploit vmatch_ptr_gl'; eauto. intros [A | [b [A B]]].
  * simpl in H; rewrite A in H; inv H.
  * simpl; rewrite volatile_load_global_charact. exists b; split; congruence.
+ simpl in H. assert (V: vmatch bc (rs#r1) (Ptr (Gl symb n1))) by (rewrite <- e1; apply MATCH). 
  exploit vmatch_ptr_gl'; eauto. intros [A | [b [A B]]].
  * simpl in H; rewrite A in H; inv H.
  * simpl; rewrite volatile_store_global_charact. exists b; split; congruence.
+ inv H. exploit annot_strength_reduction_correct; eauto. intros [eargs' [A B]]. 
  rewrite <- B. econstructor; eauto. 
Qed.

End BUILTIN_STRENGTH_REDUCTION.

(** The proof of semantic preservation is a simulation argument
  based on "option" diagrams of the following form:
<<
                 n
       st1 --------------- st2
        |                   |
       t|                   |t or (? and n' < n)
        |                   |
        v                   v
       st1'--------------- st2'
                 n'
>>
  The left vertical arrow represents a transition in the
  original RTL code.  The top horizontal bar is the [match_states]
  invariant between the initial state [st1] in the original RTL code
  and an initial state [st2] in the transformed code.
  This invariant expresses that all code fragments appearing in [st2]
  are obtained by [transf_code] transformation of the corresponding
  fragments in [st1].  Moreover, the state [st1] must match its compile-time
  approximations at the current program point.
  These two parts of the diagram are the hypotheses.  In conclusions,
  we want to prove the other two parts: the right vertical arrow,
  which is a transition in the transformed RTL code, and the bottom
  horizontal bar, which means that the [match_state] predicate holds
  between the final states [st1'] and [st2']. *)

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
   match_stackframe_intro:
      forall res sp pc rs f rs' sprog rm,
      forall (RM: rm = romem_for_program sprog)
             (SPROG: program_linksub Language_RTL sprog prog),
      regs_lessdef rs rs' ->
    match_stackframes
        (Stackframe res f sp pc rs)
        (Stackframe res (transf_function rm f) sp pc rs')
 | match_stackframe_identical:
      forall res sp pc rs rs' f
             (ENV: regset_lessdef rs rs'),
    match_stackframes
        (Stackframe res f sp pc rs)
        (Stackframe res f sp pc rs').

Inductive match_identical_states: state -> state -> Prop :=
  match_identical_states_intro:
      forall s sp pc rs m f s' rs' m'
           (STACKS: list_forall2 match_stackframes s s')
           (ENV: regset_lessdef rs rs')
           (MEM: Mem.extends m m'),
      match_identical_states (State s f sp pc rs m)
                    (State s' f sp pc rs' m').

Inductive match_states: nat -> state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m f s' pc' rs' m' bc ae n sprog rm
           (RM: rm = romem_for_program sprog)
           (SPROG: program_linksub Language_RTL sprog prog)
           (MATCH: ematch bc rs ae)
           (STACKS: list_forall2 match_stackframes s s')
           (PC: match_pc f ae n pc pc')
           (REGS: regs_lessdef rs rs')
           (MEM: Mem.extends m m'),
      match_states n (State s f sp pc rs m)
                    (State s' (transf_function rm f) sp pc' rs' m')
  | match_states_call:
      forall s f args m s' args' m' f'
           (STACKS: list_forall2 match_stackframes s s')
           (ARGS: Val.lessdef_list args args')
           (MFUN: match_fundef prog f f')
           (MEM: Mem.extends m m'),
      match_states O (Callstate s f args m)
                     (Callstate s' f' args' m')
  | match_states_return:
      forall s v m s' v' m'
           (STACKS: list_forall2 match_stackframes s s')
           (RES: Val.lessdef v v')
           (MEM: Mem.extends m m'),
      list_forall2 match_stackframes s s' ->
      match_states O (Returnstate s v m)
                     (Returnstate s' v' m')
  | match_states_identical:
      forall s s' (MATCH: match_identical_states s s'),
      match_states O s s'.

Lemma match_states_succ:
  forall s f sp pc rs m s' rs' m' sprog rm,
  forall (RM: rm = romem_for_program sprog)
         (SPROG: program_linksub Language_RTL sprog prog),
  sound_state_ext prog (State s f sp pc rs m) ->
  list_forall2 match_stackframes s s' ->
  regs_lessdef rs rs' ->
  Mem.extends m m' ->
  match_states O (State s f sp pc rs m)
                 (State s' (transf_function rm f) sp pc rs' m').
Proof.
  intros. inv H. 
  specialize (Hsound _ SPROG). inv Hsound. 
  eapply match_states_intro with (bc := bc) (ae := ae); auto. 
  constructor.
Qed.

Lemma transf_instr_at:
  forall rm f pc i,
  f.(fn_code)!pc = Some i ->
  (transf_function rm f).(fn_code)!pc = Some(transf_instr f (analyze rm f) rm pc i).
Proof.
  intros. simpl. rewrite PTree.gmap. rewrite H. auto. 
Qed.

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc (fn_code ?f) = Some ?instr),
    H2: (analyze ?rm ?f)#?pc = VA.State ?ae ?am |- _ =>
      (* fold rm in H2; *) generalize (transf_instr_at rm _ _ _ H1); unfold transf_instr; rewrite H2
  end.

(** The proof of simulation proceeds by case analysis on the transition
  taken in the source code. *)

Lemma transf_step_correct_identical:
  forall s1 t s2,
  step ge s1 t s2 ->
  forall s1' (SS1: sound_state_ext prog s1) (SS2: sound_state_ext prog s2) (MS: match_identical_states s1 s1'),
  (exists n2, exists s2', step tge s1' t s2' /\ match_states n2 s2 s2').
Proof.
  intros. destruct (is_normal s1) eqn:NORMAL1.
  { (* is_normal *)
    destruct s1; try by inv NORMAL1.
    exploit is_normal_step; eauto. i; des. subst. inv MS.
    exploit is_normal_extends; eauto using symbols_preserved, varinfo_preserved. intro. des.
    exploit is_normal_step; try apply TSTEP; eauto.
    i; des. inv S2.
    esplits; eauto using match_states_identical, match_identical_states_intro.
  }
  inv MS. unfold is_normal in NORMAL1.
  destruct (fn_code f) ! pc as [[]|] eqn:OPCODE; try by inv NORMAL1; inv H; clarify.
  - (* Icall *)
    inv H; clarify.
    exploit find_function_translated; eauto. i; des.
    esplits; eauto using exec_Icall, match_fundef_sig.
    econs; eauto using regset_lessdef_val_lessdef_list.
    econs; eauto. econs; eauto.
  - (* Itailcall *)
    inv H; clarify.
    exploit find_function_translated; eauto. i; des.
    assert (X: { m1' | Mem.free m' stk 0 (fn_stacksize f) = Some m1'}).
    { apply Mem.range_perm_free. red; intros.
      destruct (zlt ofs f.(fn_stacksize)); try omega.
      eapply Mem.perm_extends; eauto.
      eapply Mem.free_range_perm; eauto.
    }
    destruct X as [m1' FREE].
    exploit Mem.free_parallel_extends; eauto. i; des.
    rewrite FREE in H1. inv H1.
    esplits; eauto using exec_Itailcall, match_fundef_sig.
    econs; eauto using regset_lessdef_val_lessdef_list.
  - (* Ireturn *)
    inv H; clarify.
    exploit Mem.free_parallel_extends; eauto.
    intro. des.
    esplits; eauto using exec_Ireturn.
    econs; eauto.
    destruct o; eauto.
Qed.

Lemma transf_step_correct:
  forall s1 t s2,
  step ge s1 t s2 ->
  forall n1 s1' (SS1: sound_state_ext prog s1) (SS2: sound_state_ext prog s2) (MS: match_states n1 s1 s1'),
  (exists n2, exists s2', step tge s1' t s2' /\ match_states n2 s2 s2')
  \/ (exists n2, n2 < n1 /\ t = E0 /\ match_states n2 s2 s1')%nat.
Proof.
  intros s1 t s2 BACKUP_STEP. generalize BACKUP_STEP.
  induction 1; intros; inv MS;
  try (by eauto using transf_step_correct_identical);
  try (inv SS1; specialize (Hsound _ SPROG); inv Hsound; rename bc into bct; rename bc0 into bc; rename bct into bc0; rename ae into aet; rename ae0 into ae; rename aet into ae0); try (inv PC; try congruence).

  (* Inop, preserved *)
  rename pc'0 into pc. TransfInstr; intros. 
  left; econstructor; econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_states_succ; eauto.

  (* Inop, skipped over *)
  assert (s0 = pc') by congruence. subst s0.
  right; exists n; split. omega. split. auto.
  eapply match_states_intro with bc0 ae0 sprog; auto.

  (* Iop *)
  rename pc'0 into pc. TransfInstr.
  set (a := eval_static_operation op (aregs ae args)).
  set (ae' := AE.set res a ae).
  assert (VMATCH: vmatch bc v a) by (eapply eval_static_operation_sound; eauto with va).
  assert (MATCH': ematch bc (rs#res <- v) ae') by (eapply ematch_update; eauto). 
  destruct (const_for_result a) as [cop|] eqn:?; intros.
  (* constant is propagated *)
  exploit const_for_result_correct; eauto. intros (v' & A & B).
  left; econstructor; econstructor; split.
  eapply exec_Iop; eauto. 
  apply match_states_intro with bc ae' sprog; auto.
  apply match_successor. 
  apply set_reg_lessdef; auto.
  (* operator is strength-reduced *)
  assert(OP:
     let (op', args') := op_strength_reduction op args (aregs ae args) in
     exists v',
        eval_operation ge (Vptr sp0 Int.zero) op' rs ## args' m = Some v' /\
        Val.lessdef v v').
  { eapply op_strength_reduction_correct with (ae := ae); eauto with va. }
  destruct (op_strength_reduction op args (aregs ae args)) as [op' args'].
  destruct OP as [v' [EV' LD']].
  assert (EV'': exists v'', eval_operation ge (Vptr sp0 Int.zero) op' rs'##args' m' = Some v'' /\ Val.lessdef v' v'').
  { eapply eval_operation_lessdef; eauto. eapply regs_lessdef_regs; eauto. }
  destruct EV'' as [v'' [EV'' LD'']].
  left; econstructor; econstructor; split.
  eapply exec_Iop; eauto.
  erewrite eval_operation_preserved. eexact EV''. exact symbols_preserved.
  apply match_states_intro with bc ae' sprog; auto.
  apply match_successor.
  apply set_reg_lessdef; auto. eapply Val.lessdef_trans; eauto.

  (* Iload *)
  rename pc'0 into pc. TransfInstr.
  set (aa := eval_static_addressing addr (aregs ae args)).
  assert (VM1: vmatch bc a aa) by (eapply eval_static_addressing_sound; eauto with va).
  set (av := loadv chunk (romem_for_program sprog) am aa). 
  assert (VM2: vmatch bc v av) by (eapply loadv_sound; eauto). 
  destruct (const_for_result av) as [cop|] eqn:?; intros.
  (* constant-propagated *)
  exploit const_for_result_correct; eauto. intros (v' & A & B).
  left; econstructor; econstructor; split.
  eapply exec_Iop; eauto.
  eapply match_states_succ; eauto.
  apply set_reg_lessdef; auto.
  (* strength-reduced *)
  assert (ADDR:
     let (addr', args') := addr_strength_reduction addr args (aregs ae args) in
     exists a',
        eval_addressing ge (Vptr sp0 Int.zero) addr' rs ## args' = Some a' /\
        Val.lessdef a a').
  { eapply addr_strength_reduction_correct with (ae := ae); eauto with va. }
  destruct (addr_strength_reduction addr args (aregs ae args)) as [addr' args'].
  destruct ADDR as (a' & P & Q).
  exploit eval_addressing_lessdef. eapply regs_lessdef_regs; eauto. eexact P. 
  intros (a'' & U & V).
  assert (W: eval_addressing tge (Vptr sp0 Int.zero) addr' rs'##args' = Some a'').
  { rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved. }
  exploit Mem.loadv_extends. eauto. eauto. apply Val.lessdef_trans with a'; eauto.
  intros (v' & X & Y).
  left; econstructor; econstructor; split.
  eapply exec_Iload; eauto.
  eapply match_states_succ; eauto. apply set_reg_lessdef; auto.

  (* Istore *)
  rename pc'0 into pc. TransfInstr.
  assert (ADDR:
     let (addr', args') := addr_strength_reduction addr args (aregs ae args) in
     exists a',
        eval_addressing ge (Vptr sp0 Int.zero) addr' rs ## args' = Some a' /\
        Val.lessdef a a').
  { eapply addr_strength_reduction_correct with (ae := ae); eauto with va. }
  destruct (addr_strength_reduction addr args (aregs ae args)) as [addr' args'].
  destruct ADDR as (a' & P & Q).
  exploit eval_addressing_lessdef. eapply regs_lessdef_regs; eauto. eexact P. 
  intros (a'' & U & V).
  assert (W: eval_addressing tge (Vptr sp0 Int.zero) addr' rs'##args' = Some a'').
  { rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved. }
  exploit Mem.storev_extends. eauto. eauto. apply Val.lessdef_trans with a'; eauto. apply REGS. 
  intros (m2' & X & Y).
  left; econstructor; econstructor; split.
  eapply exec_Istore; eauto.
  eapply match_states_succ; eauto.

  (* Icall *)
  rename pc'0 into pc.
  exploit transf_ros_correct; eauto. intros [tf [FIND' MATCHF']].
  TransfInstr; intro.
  left; econstructor; econstructor; split.
  eapply exec_Icall; eauto. eapply match_fundef_sig; eauto.
  constructor; auto. constructor; auto.
  econstructor; eauto.
  apply regs_lessdef_regs; auto. 

  (* Itailcall *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  exploit transf_ros_correct; eauto. intros [tf [FIND' MATCHF']].
  TransfInstr; intro.
  left; econstructor; econstructor; split.
  eapply exec_Itailcall; eauto. eapply match_fundef_sig; eauto.
  constructor; auto. 
  apply regs_lessdef_regs; auto. 

  (* Ibuiltin *)
  rename pc'0 into pc.
Opaque builtin_strength_reduction.
  exploit builtin_strength_reduction_correct; eauto. 
  TransfInstr.
  destruct (builtin_strength_reduction ae ef args) as [ef' args'].
  intros P Q.
  exploit external_call_mem_extends; eauto. 
  instantiate (1 := rs'##args'). apply regs_lessdef_regs; auto.
  intros [v' [m2' [A [B [C D]]]]].
  left; econstructor; econstructor; split.
  eapply exec_Ibuiltin. eauto. 
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  eapply match_states_succ; eauto. simpl; auto.
  apply set_reg_lessdef; auto.

  (* Icond, preserved *)
  rename pc'0 into pc. TransfInstr.
  set (ac := eval_static_condition cond (aregs ae args)).
  assert (C: cmatch (eval_condition cond rs ## args m) ac)
  by (eapply eval_static_condition_sound; eauto with va).
  rewrite H0 in C.
  generalize (cond_strength_reduction_correct bc ae rs m EM cond args (aregs ae args) (refl_equal _)). 
  destruct (cond_strength_reduction cond args (aregs ae args)) as [cond' args'].
  intros EV1 TCODE.
  left; exists O; exists (State s' (transf_function (romem_for_program sprog) f) (Vptr sp0 Int.zero) (if b then ifso else ifnot) rs' m'); split. 
  destruct (resolve_branch ac) eqn: RB. 
  assert (b0 = b) by (eapply resolve_branch_sound; eauto). subst b0. 
  destruct b; eapply exec_Inop; eauto. 
  eapply exec_Icond; eauto.
  eapply eval_condition_lessdef with (vl1 := rs##args'); eauto. eapply regs_lessdef_regs; eauto. congruence.
  eapply match_states_succ; eauto. 

  (* Icond, skipped over *)
  rewrite H1 in H; inv H. 
  set (ac := eval_static_condition cond (aregs ae0 args)) in *.
  assert (C: cmatch (eval_condition cond rs ## args m) ac)
  by (eapply eval_static_condition_sound; eauto with va).
  rewrite H0 in C.
  assert (b0 = b) by (eapply resolve_branch_sound; eauto). subst b0. 
  right; exists n; split. omega. split. auto.
  econstructor; try apply H3; eauto.

  (* Ijumptable *)
  rename pc'0 into pc.
  assert (A: (fn_code (transf_function (romem_for_program sprog) f))!pc = Some(Ijumptable arg tbl)
             \/ (fn_code (transf_function (romem_for_program sprog) f))!pc = Some(Inop pc')).
  { TransfInstr.
    destruct (areg ae arg) eqn:A; auto. 
    generalize (EM arg). fold (areg ae arg); rewrite A. 
    intros V; inv V. replace n0 with n by congruence. 
    rewrite H1. auto. }
  assert (rs'#arg = Vint n). 
  { generalize (REGS arg). rewrite H0. intros LD; inv LD; auto. }
  left; exists O; exists (State s' (transf_function (romem_for_program sprog) f) (Vptr sp0 Int.zero) pc' rs' m'); split.
  destruct A. eapply exec_Ijumptable; eauto. eapply exec_Inop; eauto.
  eapply match_states_succ; eauto.

  (* Ireturn *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  left; exists O; exists (Returnstate s' (regmap_optget or Vundef rs') m2'); split.
  eapply exec_Ireturn; eauto. TransfInstr; auto.
  constructor; auto.
  destruct or; simpl; auto. 

  (* internal function *)
  exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl.
  intros [m2' [A B]].
  inv MFUN.
    (* transl *)
  assert (X: exists bc ae, ematch bc (init_regs args (fn_params f)) ae).
  { inv SS2. specialize (Hsound _ SPROG). inv Hsound. exists bc; exists ae; auto. }
  destruct X as (bc1 & ae1 & MATCH).
  simpl. unfold transf_function.
  left; exists O; econstructor; split.
  eapply exec_function_internal; simpl; eauto.
  simpl. econstructor; eauto.
  constructor. 
  apply init_regs_lessdef; auto.
    (* identical *)
  left; exists O; econstructor; split.
  eapply exec_function_internal; simpl; eauto.
  apply match_states_identical. econstructor; eauto.
  apply regset_lessdef_init_regs; auto.

  (* external function *)
  exploit external_call_mem_extends; eauto. 
  intros [v' [m2' [A [B [C D]]]]].
  assert (f' = External ef) by (inv MFUN; auto). subst.
  simpl. left; econstructor; econstructor; split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.

  (* return *)
  inv STACKS. inv H1.
    (* transl *)
  assert (X: exists bc ae, ematch bc (rs#res <- vres) ae).
  { inv SS2. specialize (Hsound _ SPROG). inv Hsound. exists bc; exists ae; auto. }
  destruct X as (bc1 & ae1 & MATCH).
  left; exists O; econstructor; split.
  eapply exec_return; eauto. 
  econstructor; eauto. constructor. apply set_reg_lessdef; auto. 
    (* identical *)
  left; exists O; econstructor; split.
  eapply exec_return; eauto. apply match_states_identical. 
  econstructor; eauto.
  apply regset_lessdef_set_reg; auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists n, exists st2, initial_state tprog st2 /\ match_states n st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intros [tf [FIND MFUN]].
  exists O; exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
  apply (init_mem_transf_optionally _ _ TRANSF); auto.
  replace (prog_main tprog) with (prog_main prog); [|by inv TRANSF].
  rewrite symbols_preserved. eauto.
  rewrite <- H3. eapply match_fundef_sig; eauto.
  constructor; auto. constructor. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall n st1 st2 r, 
  match_states n st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. inv RES. constructor. 
  inv MATCH.
Qed.

(** The preservation of the observable behavior of the program then
  follows. *)

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  apply Forward_simulation with
     (fsim_order := lt)
     (fsim_match_states := fun n s1 s2 => sound_state_ext prog s1 /\ match_states n s1 s2).
- apply lt_wf.
- simpl; intros. exploit transf_initial_states; eauto. intros (n & st2 & A & B).
  exists n, st2; intuition. eapply sound_initial; eauto. 
- simpl; intros. destruct H. eapply transf_final_states; eauto. 
- simpl; intros. destruct H0.
  assert (sound_state_ext prog s1') by (eapply sound_past_step; eauto).
  fold ge; fold tge.
  exploit transf_step_correct; eauto. 
  intros [ [n2 [s2' [A B]]] | [n2 [A [B C]]]].
  exists n2; exists s2'; split; auto. left; apply plus_one; auto.
  exists n2; exists s2; split; auto. right; split; auto. subst t; apply star_refl. 
- eexact symbols_preserved.
Qed.

End PRESERVATION.

(* new *) Lemma Constprop_sepcomp_rel
(* new *)       rtlprog1 rtlprog2
(* new *)       (Htrans: Constprop.transf_program rtlprog1 = rtlprog2 \/ rtlprog1 = rtlprog2):
(* new *)   @sepcomp_rel
(* new *)     Language.Language_RTL Language.Language_RTL
(* new *)     (fun p f tf => Constprop.transf_function (romem_for_program p) f = tf \/ f = tf)
(* new *)     (fun p ef tef => ef = tef)
(* new *)     (@Errors.OK _)
(* new *)     rtlprog1 rtlprog2.
(* new *) Proof.
(* new *)   inv Htrans.
(* new *)   - apply transf_program_optionally_sepcomp_rel.
(* new *)     unfold Constprop.transf_program. f_equal.
(* new *)     apply Axioms.functional_extensionality. intro fd.
(* new *)     destruct fd; auto.
(* new *)   - apply transf_program_optionally_sepcomp_rel_identical. auto.
(* new *) Qed.
