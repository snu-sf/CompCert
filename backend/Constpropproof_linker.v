Require Import Classical.
Require Import WFType paco.
Require Import Coqlib.
Require Import Maps Maps_linker.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Language Linker Linkeq.
Require Import ProgramLSim FunctionLSim.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Kildall.
Require Import ValueDomain.
Require Import ValueAOp.
Require Import ValueAnalysis.
Require Import CSEdomain.
Require Import CombineOp.
Require Import CombineOpproof.
Require Import ConstpropOp.
Require Import Constprop.
Require Import ConstpropOpproof.
Require Import Constpropproof.
Require Import RTL_linker ValueAnalysis_linker.

Set Implicit Arguments.

Section PRESERVATION.

Variable (prog tprog: program).
Hypothesis TRANSF: transf_program prog = tprog.

Section FUTURE.

Variable (fprog ftprog:program).
Hypothesis (Hfsim: @program_weak_lsim Language_RTL Language_RTL transf_sigT transf_efT transf_vT
                                      fprog ftprog).

Hypothesis (Hfprog: program_linkeq Language_RTL prog fprog).
Hypothesis (Hftprog: program_linkeq Language_RTL tprog ftprog).

Let ge := Genv.globalenv fprog.
Let tge := Genv.globalenv ftprog.

Lemma transf_ros_correct:
  forall bc rs ae ros f rs',
  genv_match bc ge ->
  ematch bc rs ae ->
  find_function ge ros rs = Some f ->
  regs_lessdef rs rs' ->
  exists f',
  find_function tge (transf_ros ae ros) rs' = Some f' /\
  globfun_weak_lsim Language_RTL Language_RTL transf_sigT transf_efT ge tge f f'.
Proof.
  intros until rs'; intros GE EM FF RLD.
  eapply find_function_translated_Constprop; eauto.
  destruct ros; simpl in *.
- (* function pointer *)
  generalize (EM r); fold (areg ae r); intro VM. generalize (RLD r); intro LD.
  destruct (areg ae r); auto. destruct p; auto. 
  predSpec Int.eq Int.eq_spec ofs Int.zero; intros; auto. 
  subst ofs. exploit vmatch_ptr_gl; eauto. intros LD'. inv LD'; try discriminate.
  rewrite H1 in FF. unfold Genv.symbol_address in FF. 
  simpl. fold ge. destruct (Genv.find_symbol ge id) as [b|]; try discriminate.
  simpl in FF. rewrite dec_eq_true in FF. auto.
  rewrite <- H0 in FF; discriminate.
- (* function symbol *)
  fold ge. destruct (Genv.find_symbol ge i) as [b|]; try discriminate. auto.
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
    unfold Genv.symbol_address. unfold ge. erewrite <- symbols_preserved; eauto. reflexivity.
    eapply vmatch_ptr_gl; eauto. 
  + (* stack *)
    inv H. exists (Vptr sp ofs); split. 
    simpl; rewrite Int.add_zero_l; auto. 
    eapply vmatch_ptr_stk; eauto. 
Qed.

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
   match_stackframe_intro:
      forall res sp pc rs f rs' rm,
      regs_lessdef rs rs' ->
      PTree_le rm (romem_for_program fprog) ->
    match_stackframes
        (Stackframe res f sp pc rs)
        (Stackframe res (transf_function rm f) sp pc rs').

Inductive match_states: nat -> state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m f s' pc' rs' m' bc ae n rm
           (MATCH: ematch bc rs ae)
           (STACKS: list_forall2 match_stackframes s s')
           (PC: match_pc f ae n pc pc')
           (REGS: regs_lessdef rs rs')
           (MEM: Mem.extends m m')
           (RM: PTree_le rm (romem_for_program fprog)),
      match_states n (State s f sp pc rs m)
                    (State s' (transf_function rm f) sp pc' rs' m')
  | match_states_return:
      forall s v m s' v' m'
           (STACKS: list_forall2 match_stackframes s s')
           (RES: Val.lessdef v v')
           (MEM: Mem.extends m m'),
      list_forall2 match_stackframes s s' ->
      match_states O (Returnstate s v m)
                     (Returnstate s' v' m').

Inductive match_call: nat -> state -> state -> Prop :=
  | match_states_call:
      forall s f args m s' f' args' m'
           (STACKS: list_forall2 match_stackframes s s')
           (FUN: globfun_weak_lsim Language_RTL Language_RTL transf_sigT transf_efT ge tge f f')
           (ARGS: Val.lessdef_list args args')
           (MEM: Mem.extends m m'),
      match_call O (Callstate s f args m)
                   (Callstate s' f' args' m').

Lemma match_states_succ:
  forall s f sp pc rs m s' rs' m' rm,
  sound_state_ext fprog (State s f sp pc rs m) ->
  list_forall2 match_stackframes s s' ->
  regs_lessdef rs rs' ->
  Mem.extends m m' ->
  PTree_le rm (romem_for_program fprog) ->
  match_states O (State s f sp pc rs m)
                 (State s' (transf_function rm f) sp pc rs' m').
Proof.
  intros. inv H. specialize (Hsound _ H3). inv Hsound.
  apply match_states_intro with (bc := bc) (ae := ae); auto. 
  constructor.
Qed.

Lemma transf_instr_at:
  forall f pc i rm,
  f.(fn_code)!pc = Some i ->
  (transf_function rm f).(fn_code)!pc = Some(transf_instr f (analyze rm f) rm pc i).
Proof.
  intros. simpl. rewrite PTree.gmap. rewrite H. auto. 
Qed.

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc (fn_code ?f) = Some ?instr),
    H2: (analyze ?rm ?f)#?pc = VA.State ?ae ?am |- _ =>
      (* fold rm in H2; *) generalize (transf_instr_at _ _ rm H1); unfold transf_instr; rewrite H2
  end.

Lemma transf_step_correct:
  forall s1 t s2,
  step ge s1 t s2 ->
  forall n1 s1' (SS1: sound_state_ext fprog s1) (SS2: sound_state_ext fprog s2) (MS: match_states n1 s1 s1'),
  (exists n2, exists s2', step tge s1' t s2' /\ (match_states n2 s2 s2' \/ match_call n2 s2 s2'))
  \/ (exists n2, n2 < n1 /\ t = E0 /\ (match_states n2 s2 s1' \/ match_call n2 s2 s1'))%nat.
Proof.
  induction 1; intros; inv MS; try (inv SS1; specialize (Hsound _ RM); inv Hsound; rename bc into bct; rename bc0 into bc; rename bct into bc0; rename ae into aet; rename ae0 into ae; rename aet into ae0); try (inv PC; try congruence).

  (* Inop, preserved *)
  rename pc'0 into pc. TransfInstr; intros. 
  left; econstructor; econstructor; split.
  eapply exec_Inop; eauto.
  left. eapply match_states_succ; eauto.

  (* Inop, skipped over *)
  assert (s0 = pc') by congruence. subst s0.
  right; exists n; split. omega. split. auto.
  left. apply match_states_intro with bc0 ae0; auto.

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
  left. apply match_states_intro with bc ae'; auto.
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
  erewrite eval_operation_preserved. eexact EV''. apply symbols_preserved. auto.
  left. apply match_states_intro with bc ae'; auto.
  apply match_successor.
  apply set_reg_lessdef; auto. eapply Val.lessdef_trans; eauto.

  (* Iload *)
  rename pc'0 into pc. TransfInstr.
  set (aa := eval_static_addressing addr (aregs ae args)).
  assert (VM1: vmatch bc a aa) by (eapply eval_static_addressing_sound; eauto with va).
  set (av := loadv chunk rm am aa). 
  assert (VM2: vmatch bc v av) by (eapply loadv_sound; eauto). 
  destruct (const_for_result av) as [cop|] eqn:?; intros.
  (* constant-propagated *)
  exploit const_for_result_correct; eauto. intros (v' & A & B).
  left; econstructor; econstructor; split.
  eapply exec_Iop; eauto.
  left. eapply match_states_succ; eauto.
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
  { rewrite <- U. apply eval_addressing_preserved. apply symbols_preserved. auto. }
  exploit Mem.loadv_extends. eauto. eauto. apply Val.lessdef_trans with a'; eauto.
  intros (v' & X & Y).
  left; econstructor; econstructor; split.
  eapply exec_Iload; eauto.
  left. eapply match_states_succ; eauto. apply set_reg_lessdef; auto.

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
  { rewrite <- U. apply eval_addressing_preserved. apply symbols_preserved. auto. }
  exploit Mem.storev_extends. eauto. eauto. apply Val.lessdef_trans with a'; eauto. apply REGS. 
  intros (m2' & X & Y).
  left; econstructor; econstructor; split.
  eapply exec_Istore; eauto.
  left. eapply match_states_succ; eauto.

  (* Icall *)
  rename pc'0 into pc.
  exploit transf_ros_correct; eauto. intros [tf [FIND' TRANSF']].
  TransfInstr; intro.
  left; econstructor; econstructor; split.
  eapply exec_Icall; eauto. eapply sig_preserved. eauto.
  right. constructor; auto. constructor; auto.
  econstructor; eauto.
  apply regs_lessdef_regs; auto. 

  (* Itailcall *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  exploit transf_ros_correct; eauto. intros [tf [FIND' TRANSF']].
  TransfInstr; intro.
  left; econstructor; econstructor; split.
  eapply exec_Itailcall; eauto. eapply sig_preserved. eauto.
  right. constructor; auto. 
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
  apply symbols_preserved. auto. apply varinfo_preserved. auto.
  left. eapply match_states_succ; eauto. simpl; auto.
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
  left; exists O; exists (State s' (transf_function rm f) (Vptr sp0 Int.zero) (if b then ifso else ifnot) rs' m'); split. 
  destruct (resolve_branch ac) eqn: RB. 
  assert (b0 = b) by (eapply resolve_branch_sound; eauto). subst b0. 
  destruct b; eapply exec_Inop; eauto. 
  eapply exec_Icond; eauto.
  eapply eval_condition_lessdef with (vl1 := rs##args'); eauto. eapply regs_lessdef_regs; eauto. congruence.
  left. eapply match_states_succ; eauto. 

  (* Icond, skipped over *)
  rewrite H1 in H; inv H. 
  set (ac := eval_static_condition cond (aregs ae0 args)) in *.
  assert (C: cmatch (eval_condition cond rs ## args m) ac)
  by (eapply eval_static_condition_sound; eauto with va).
  rewrite H0 in C.
  assert (b0 = b) by (eapply resolve_branch_sound; eauto). subst b0. 
  right; exists n; split. omega. split. auto.
  left. econstructor; try apply H3; eauto.

  (* Ijumptable *)
  rename pc'0 into pc.
  assert (A: (fn_code (transf_function rm f))!pc = Some(Ijumptable arg tbl)
             \/ (fn_code (transf_function rm f))!pc = Some(Inop pc')).
  { TransfInstr.
    destruct (areg ae arg) eqn:A; auto. 
    generalize (EM arg). fold (areg ae arg); rewrite A. 
    intros V; inv V. replace n0 with n by congruence. 
    rewrite H1. auto. }
  assert (rs'#arg = Vint n). 
  { generalize (REGS arg). rewrite H0. intros LD; inv LD; auto. }
  left; exists O; exists (State s' (transf_function rm f) (Vptr sp0 Int.zero) pc' rs' m'); split.
  destruct A. eapply exec_Ijumptable; eauto. eapply exec_Inop; eauto.
  left. eapply match_states_succ; eauto.

  (* Ireturn *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  left; exists O; exists (Returnstate s' (regmap_optget or Vundef rs') m2'); split.
  eapply exec_Ireturn; eauto. TransfInstr; auto.
  left. constructor; auto.
  destruct or; simpl; auto. 

  (* (* internal function *) *)
  (* exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl. *)
  (* intros [m2' [A B]]. *)
  (* assert (X: exists bc ae, ematch bc (init_regs args (fn_params f)) ae). *)
  (* { inv SS2. exists bc0; exists ae; auto. } *)
  (* destruct X as (bc1 & ae1 & MATCH). *)
  (* simpl. unfold transf_function. *)
  (* left; exists O; econstructor; split. *)
  (* eapply exec_function_internal; simpl; eauto. *)
  (* simpl. econstructor; eauto. *)
  (* constructor.  *)
  (* apply init_regs_lessdef; auto. *)

  (* (* external function *) *)
  (* exploit external_call_mem_extends; eauto.  *)
  (* intros [v' [m2' [A [B [C D]]]]]. *)
  (* simpl. left; econstructor; econstructor; split. *)
  (* eapply exec_function_external; eauto. *)
  (* eapply external_call_symbols_preserved; eauto. *)
  (* exact symbols_preserved. exact varinfo_preserved. *)
  (* constructor; auto. *)

  (* return *)
  assert (X: exists bc ae, ematch bc (rs#res <- vres) ae).
  { inv SS2. exploit Hsound; [reflexivity|]. intro X. inv X. exists bc; exists ae; auto. }
  destruct X as (bc1 & ae1 & MATCH).
  inv H4. inv H1. 
  left; exists O; econstructor; split.
  eapply exec_return; eauto. 
  left. econstructor; eauto. constructor. apply set_reg_lessdef; auto. 
Qed.

Lemma transf_initial_states:
  forall st1, initial_state fprog st1 ->
  exists n, exists st2, initial_state ftprog st2 /\ match_call n st1 st2.
Proof.
  intros. inversion H. 
  exploit funct_ptr_translated; eauto. intros [tf [A B]].
  eexists. exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
  eapply (@program_lsim_init_mem_match Language_RTL Language_RTL); try apply transf_efT_sigT; eauto.
  replace (prog_main ftprog) with (prog_main fprog).
  erewrite symbols_preserved; eauto.
  destruct Hfsim as [_ Hmain]. unfold fundef in *. simpl in *. rewrite <- Hmain. auto.
  rewrite <- H3. eapply sig_preserved; eauto.
  constructor. constructor. auto. auto. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall n st1 st2 r, 
  match_states n st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. inv RES. constructor. 
Qed.

Inductive match_states_ext i st tst: Prop :=
| match_states_ext_intro
    (Hsrc: sound_state_ext fprog st)
    (Htgt: sound_state_ext ftprog tst)
    (Hmatch: match_states i st tst)
.

End FUTURE.

(* memory relation *)

Inductive mrelT_sem (mrel:unit) (fprog ftprog:program) (i:WF.t) (s1 s2:state): Prop :=
| mrelT_sem_intro n
    (MEASURE: i = WF.from_nat n)
    (Hsrc: sound_state_ext fprog s1)
    (Htgt: sound_state_ext ftprog s2)
    (MS: match_states fprog n s1 s2 \/ match_call fprog ftprog n s1 s2)
.

Definition mrelT_ops: mrelT_opsT Language_ext_RTL Language_ext_RTL unit :=
  mkmrelT_opsT
    Language_ext_RTL Language_ext_RTL
    mrelT_sem
    (fun _ v1 v2 => Val.lessdef v1 v2)
    (fun _ _ => True)
    (fun _ _ => True).

Lemma mrelT_ops_lessdef_list mrel v1 v2:
  Val.lessdef_list v1 v2 <-> list_forall2 (mrelT_ops.(sem_value) mrel) v1 v2.
Proof.
  revert v2.
  induction v1; intros; constructor; intro H; inv H; constructor; auto.
  - apply IHv1. auto.
  - apply IHv1. auto.
Qed.

Program Definition mrelT_props:
  @mrelT_propsT Language_ext_RTL Language_ext_RTL
                transf_sigT transf_efT transf_vT _ mrelT_ops :=
  mkmrelT_propsT _ _ _ _ _ _ _.
Next Obligation. repeat constructor. Qed.
Next Obligation. repeat constructor. Qed.
Next Obligation. inv H. auto. Qed.
Next Obligation.
  apply initial_state_equiv in H1. apply initial_state_equiv in H2.
  exploit transf_initial_states; eauto. intros [n2 [s2' [Hs2' Hinit]]].
  generalize (initial_state_unique Hs2' H2). intro. subst.
  exists tt. eexists. econstructor; auto.
  - apply sound_initial. auto.
  - apply sound_initial. auto.
  - right. eauto.
Qed.
Next Obligation.
  apply (mrelT_ops_lessdef_list mrel args1 args2) in Hargs.
  destruct fd1; inv Hfd1. destruct fd2; inv Hfd2.
  inv Hs0. inv Hmrel. destruct MS as [MS|MS]; inv MS.

  (* external function *)
  exploit external_call_mem_extends; eauto.
  intros [v' [m2' [A [B [C D]]]]].
  eexists. eexists. eexists. eexists. eexists. exists tt. eexists.
  repeat (split; [eauto; fail|]).
  cut (step (Genv.globalenv p2) (Callstate es2 (External ef2) args2 m2) evt (Returnstate es2 v' m2')).
  { intro S. split; eauto. split; auto. econstructor; eauto.
    - eapply sound_past_step; eauto. econstructor. eauto.
    - eapply sound_past_step; eauto.
    - left. econstructor; eauto.
  }
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto.
  apply symbols_preserved. auto. apply varinfo_preserved. auto.
Qed.

Section STATE_LSIM.
  
Variable (fprog ftprog:program).
Hypothesis (Hfsim: @program_weak_lsim Language_RTL Language_RTL transf_sigT transf_efT transf_vT
                                      fprog ftprog).

Hypothesis (Hfprog: program_linkeq Language_RTL prog fprog).
Hypothesis (Hftprog: program_linkeq Language_RTL tprog ftprog).

Lemma match_states_state_lsim es es' eF F i s1 s1'
      (MS: match_states_ext fprog ftprog i s1 s1'):
  @state_lsim Language_ext_RTL Language_ext_RTL transf_sigT transf_efT _
              mrelT_ops fprog ftprog es es' eF F (WF.from_nat i) s1 s1'.
Proof.
  revert F i s1 s1' MS. pcofix CIH. intros F i s1 s1' MS. pfold.
  inversion MS. destruct (classic (exists r, final_state s1 r)).
  { destruct H as [rval Hrval]. eapply _state_lsim_term; eauto.
    - apply final_state_equiv. eauto.
    - apply final_state_equiv. eapply transf_final_states; eauto.
  }
  constructor; auto.
  { repeat intro. apply H. exists r0. apply final_state_equiv. auto. }
  intros. exploit transf_step_correct; eauto; simpl.
  { eapply sound_past_step; eauto. }
  intros [[n2 [s2' [Hs2' Hmatch2]]]|[n2 [Hmeasure [Hevt Hmatch2]]]].
  { eexists. exists s2'. exists tt.
    split; [destruct Hmatch2; left; apply plus_one; auto|].
    split; auto. split; [econstructor; eauto|].
    { eapply sound_past_step; eauto. }
    { eapply sound_past_step; eauto. }
    destruct Hmatch2 as [Hmatch2|Hmatch2].
    - apply _state_lsim_or_csim_lsim. right. apply CIH.
      constructor; auto.
      + eapply sound_past_step; eauto.
      + eapply sound_past_step; eauto.
    - inversion Hmatch2. subst. eapply _state_lsim_or_csim_csim; eauto.
      + apply (mrelT_ops_lessdef_list tt). auto.
      + econstructor; eauto.
        * eapply sound_past_step; eauto.
        * eapply sound_past_step; eauto.
      + intros. subst. inversion Hst2_mem. subst. destruct MS0 as [MS0|MS0]; [|inv MS0].
        right. apply CIH. constructor; auto.
  }
  { eexists. exists s1'. exists tt.
    split; [right; split; [subst; econstructor|constructor; eauto]|].
    split; [auto|].
    split; [econstructor; eauto|].
    { eapply sound_past_step; eauto. }
    destruct Hmatch2 as [Hmatch2|Hmatch2].
    - apply _state_lsim_or_csim_lsim. right. apply CIH.
      constructor; auto.
      eapply sound_past_step; eauto.
    - inversion Hmatch2. subst. eapply _state_lsim_or_csim_csim; eauto.
      + apply (mrelT_ops_lessdef_list tt). auto.
      + econstructor; eauto.
        eapply sound_past_step; eauto.
      + intros. subst. inversion Hst2_mem. subst. destruct MS0 as [MS0|MS0]; [|inv MS0].
        right. apply CIH. constructor; auto.
  }
Qed.

Lemma transf_function_lsim f:
  @function_lsim Language_ext_RTL Language_ext_RTL transf_sigT transf_efT _
                 mrelT_ops fprog ftprog f (transf_function (romem_for_program prog) f).
Proof.
  constructor. intros. pfold. constructor; subst; auto.
  { intros ? Hfinal. apply final_state_equiv in Hfinal. inv Hfinal. }
  intros. destruct fd_src; inv Hfd_src. destruct fd_tgt; inv Hfd_tgt. inversion Hst2_src. subst.
  inv Hmrel_entry. destruct MS as [MS|MS]; inversion MS; subst.

  (* internal function *)
  exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl.
  intros [m2' [A B]].
  assert (X: exists bc ae, ematch bc (init_regs args_src (fn_params f)) ae).
  { exploit sound_past_step; eauto. intro X. inv X.
    exploit Hsound. apply program_linkeq_romem_le; eauto. intro X. inv X.
    eexists. eexists. eauto.
  }
  destruct X as (bc1 & ae1 & MATCH).
  simpl. unfold transf_function.
  exists (WF.from_nat O). eexists. exists tt. split.
  left. apply plus_one. constructor; eauto.
  simpl. split; [auto|].
  assert (Hstep: step (Genv.globalenv ftprog)
                      (Callstate es_tgt
                                 (Internal (transf_function (romem_for_program prog) f)) args_tgt
                                 mem_entry_tgt) E0
                      (State es_tgt
                             {|
                               fn_sig := fn_sig f;
                               fn_params := fn_params f;
                               fn_stacksize := fn_stacksize f;
                               fn_code := PTree.map
                                            (transf_instr f (analyze (romem_for_program prog) f)
                                                          (romem_for_program prog)) (fn_code f);
                               fn_entrypoint := fn_entrypoint f |} (Vptr stk Int.zero)
                             (fn_entrypoint f) (init_regs args_tgt (fn_params f)) m2')).
  { apply (exec_function_internal _ es_tgt (transf_function (romem_for_program prog) f)). eauto. }
  cut (match_states fprog 0
                    (State es_src f (Vptr stk Int.zero) (fn_entrypoint f)
                           (init_regs args_src (fn_params f)) m')
                    (State es_tgt
                           {|
                             fn_sig := fn_sig f;
                             fn_params := fn_params f;
                             fn_stacksize := fn_stacksize f;
                             fn_code := PTree.map
                                          (transf_instr f (analyze (romem_for_program prog) f)
                                                        (romem_for_program prog)) (fn_code f);
                             fn_entrypoint := fn_entrypoint f |} (Vptr stk Int.zero)
                           (fn_entrypoint f) (init_regs args_tgt (fn_params f)) m2')).
  { intro MS2. split; [econstructor; eauto|].
    { eapply sound_past_step; eauto. }
    { eapply sound_past_step; eauto. }
    constructor. left. apply match_states_state_lsim. constructor; auto.
    - eapply sound_past_step; eauto.
    - eapply sound_past_step; eauto.
  }
  econstructor; eauto.
  constructor.
  apply init_regs_lessdef; auto.
  apply program_linkeq_romem_le. auto.
Qed.

End STATE_LSIM.

Lemma Constprop_program_lsim:
  @program_lsim Language_RTL Language_RTL transf_sigT transf_efT transf_vT
                (@function_lsim Language_ext_RTL Language_ext_RTL transf_sigT transf_efT _ mrelT_ops)
                prog tprog.
Proof.
  generalize transf_function_lsim.
  destruct prog as [defs main]. simpl in *.
  unfold transf_program, transform_program in TRANSF.
  inv TRANSF. intro Hlsim. constructor; simpl; auto.
  revert Hlsim.
  generalize defs at 1 2 3 4 5 6 7 8 10 as fdefs. revert defs.
  induction defs; simpl; intros fdefs Hlsim; simpl; [constructor|].
  destruct a. destruct g.
  - constructor; simpl in *; try apply IHdefs; auto.
    split; auto. apply (@globdef_lsim_fun Language_RTL Language_RTL).
    destruct f; simpl in *.
    + eapply globfun_lsim_intro; eauto; simpl; auto.
      split; auto. repeat intro.
      apply Hlsim; auto.
    + eapply globfun_lsim_intro; eauto; simpl; auto.
  - constructor; simpl in *; try apply IHdefs; auto.
    split; auto. apply (@globdef_lsim_var Language_RTL Language_RTL).
    repeat constructor. destruct v; auto.
Qed.

End PRESERVATION.
