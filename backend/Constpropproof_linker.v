Require Import Classical.
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
Require Import LinkerSpecification Linkeq.
Require Import ProgramLSim.
Require Import RTLLSim ValueAnalysis_linker.
Require Import WFType paco.

Set Implicit Arguments.

Section PRESERVATION.

Let transf_V (v_src:unit) := OK v_src.
Let fundef_dec := (@common_fundef_dec function).

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: transf_program prog = tprog.

Section FUTURE.

Variable (fprog ftprog:program).
Hypothesis (Hfsim:
              program_weak_lsim
                fundef_dec fn_sig fundef_dec fn_sig transf_V
                fprog ftprog).

Hypothesis (Hfprog: program_linkeq (@common_fundef_dec function) prog fprog).
Hypothesis (Hftprog: program_linkeq (@common_fundef_dec function) tprog ftprog).

Let globfun_weak_lsim :=
  globfun_lsim fundef_dec fn_sig fundef_dec fn_sig (fun _ _ _ _ => True) fprog ftprog.

Let ge := Genv.globalenv fprog.
Let tge := Genv.globalenv ftprog.

Let rm := romem_for_program prog.

Lemma rm_frm: PTree_le rm (romem_for_program fprog).
Proof. apply program_linkeq_romem_le. auto. Qed.

Lemma transf_ros_correct:
  forall bc rs ae ros f rs',
  genv_match bc ge ->
  ematch bc rs ae ->
  find_function ge ros rs = Some f ->
  regs_lessdef rs rs' ->
  exists f',
  find_function tge (transf_ros ae ros) rs' = Some f' /\
  fundef_weak_lsim
    (@common_fundef_dec function) fn_sig
    (@common_fundef_dec function) fn_sig
    ge tge f f'.
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
      forall res sp pc rs f rs',
      regs_lessdef rs rs' ->
    match_stackframes
        (Stackframe res f sp pc rs)
        (Stackframe res (transf_function rm f) sp pc rs').

Inductive match_stackframes_ext (es es':list stackframe): list stackframe -> list stackframe -> Prop :=
  | match_stackframes_ext_nil:
      match_stackframes_ext es es' es es'
  | match_stackframes_ext_cons s s' fr fr'
      (HS: match_stackframes_ext es es' s s')
      (HFR: match_stackframes fr fr'):
      match_stackframes_ext es es' (fr::s) (fr'::s')
.

Inductive match_states (es es':list stackframe): nat -> state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m f s' pc' rs' m' bc ae n
           (MATCH: ematch bc rs ae)
           (STACKS: match_stackframes_ext es es' s s')
           (PC: match_pc f ae n pc pc')
           (REGS: regs_lessdef rs rs')
           (MEM: Mem.extends m m'),
      match_states es es'
                   n (State s f sp pc rs m)
                    (State s' (transf_function rm f) sp pc' rs' m')
  | match_states_return:
      forall s v m s' v' m'
           (STACKS: match_stackframes_ext es es' s s')
           (RES: Val.lessdef v v')
           (MEM: Mem.extends m m'),
      match_stackframes_ext es es' s s' ->
      match_states es es'
                   O (Returnstate s v m)
                     (Returnstate s' v' m').

Inductive match_call (es es':list stackframe): nat -> state -> state -> Prop :=
  | match_states_call:
      forall s f args m s' f' args' m'
           (STACKS: match_stackframes_ext es es' s s')
           (FUNCTION: fundef_weak_lsim
                        (common_fundef_dec (F:=function)) fn_sig
                        (common_fundef_dec (F:=function)) fn_sig
                        ge tge f f')
           (ARGS: Val.lessdef_list args args')
           (MEM: Mem.extends m m'),
      match_call es es'
                 O (Callstate s f args m)
                   (Callstate s' f' args' m').

Inductive match_return (es es':list stackframe): state -> state -> Prop :=
  | match_return_intro:
      forall v m v' m'
           (STACKS: match_stackframes_ext es es' es es')
           (RES: Val.lessdef v v')
           (MEM: Mem.extends m m'),
      match_stackframes_ext es es' es es' ->
      match_return es es'
                   (Returnstate es v m)
                   (Returnstate es' v' m').

Lemma match_states_succ:
  forall es es' s f sp pc rs m s' rs' m',
  sound_state_ext fprog (State s f sp pc rs m) ->
  match_stackframes_ext es es' s s' ->
  regs_lessdef rs rs' ->
  Mem.extends m m' ->
  match_states es es'
               O (State s f sp pc rs m)
                 (State s' (transf_function rm f) sp pc rs' m').
Proof.
  intros. inv H. specialize (Hsound _ rm_frm). inv Hsound.
  apply match_states_intro with (bc := bc) (ae := ae); auto. 
  constructor.
Qed.

Lemma transf_instr_at:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  (transf_function rm f).(fn_code)!pc = Some(transf_instr f (analyze rm f) rm pc i).
Proof.
  intros. simpl. rewrite PTree.gmap. rewrite H. auto. 
Qed.

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc (fn_code ?f) = Some ?instr),
    H2: (analyze ?rm ?f)#?pc = VA.State ?ae ?am |- _ =>
      (* fold rm in H2; *) generalize (@transf_instr_at _ _ _ H1); unfold transf_instr; rewrite H2
  end.

(** The proof of simulation proceeds by case analysis on the transition
  taken in the source code. *)

Lemma transf_step_correct:
  forall es es' s1 t s2,
  step ge s1 t s2 ->
  forall n1 s1' (NMR: ~ match_return es es' s1 s1') (SS1: sound_state_ext fprog s1) (SS2: sound_state_ext fprog s2) (MS: match_states es es' n1 s1 s1'),
  (exists n2, exists s2', step tge s1' t s2' /\ (match_states es es' n2 s2 s2' \/ match_call es es' n2 s2 s2'))
  \/ (exists n2, n2 < n1 /\ t = E0 /\ (match_states es es' n2 s2 s1' \/ match_call es es' n2 s2 s1'))%nat.
Proof.
  induction 1; intros; inv SS1; specialize (Hsound _ rm_frm); inv Hsound; inv MS; try (inv PC; try congruence).

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
  rename pc' into pc. TransfInstr.
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
  left. econstructor; eauto.

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
  { inv SS2. specialize (Hsound _ rm_frm). inv Hsound. exists bc0; exists ae; auto. }
  destruct X as (bc1 & ae1 & MATCH).
  inv H4; [contradict NMR; constructor; auto|].
  inv HFR.
  left; exists O; econstructor; split.
  eapply exec_return; eauto. 
  left. econstructor; eauto. constructor. apply set_reg_lessdef; auto. 
Qed.

Inductive match_states_ext es es' n st tst: Prop :=
| match_states_ext_intro
    (Hmatch: match_states es es' n st tst)
    (Hsrc: sound_state_ext fprog st)
    (Htgt: sound_state_ext ftprog tst)
.

(* TODO *)

End FUTURE.

(* TODO *)

End PRESERVATION.
