Require Import Classical.
Require Import Coqlib.
Require Import Maps Maps_linker.
Require Import Errors.
Require Import Postorder.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Renumber.
Require Import Renumberproof.
Require Import LinkerSpecification Linkeq.
Require Import ProgramLSim.
Require Import RTLLSim.
Require Import WFType paco.

Set Implicit Arguments.

Section PRESERVATION.

Variable (prog tprog: program).
Hypothesis TRANSF: transf_program prog = tprog.

Section FUTURE.

Variable (fprog ftprog:program).
Hypothesis (Hfsim: @program_weak_lsim Language_RTL Language_RTL id (@Errors.OK _) transf_V
                                      fprog ftprog).

Hypothesis (Hfprog: program_linkeq Language_RTL prog fprog).
Hypothesis (Hftprog: program_linkeq Language_RTL tprog ftprog).

Let globfun_weak_lsim :=
  @globfun_lsim Language_RTL Language_RTL id (@Errors.OK _)
                (fun _ _ _ _ => True)
                fprog ftprog.

Let ge := Genv.globalenv fprog.
Let tge := Genv.globalenv ftprog.

Ltac TR_AT :=
  match goal with
  | [ A: (fn_code _)!_ = Some _ , B: reach _ _ |- _ ] =>
        generalize (transf_function_at _ _ _ A B); simpl renum_instr; intros
  end.

Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_frames_intro: forall res f sp pc rs
        (REACH: reach f pc),
      match_frames (Stackframe res f sp pc rs)
                   (Stackframe res (transf_function f) sp (renum_pc (pnum f) pc) rs).

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk'
        (STACKS: list_forall2 match_frames stk stk')
        (REACH: reach f pc),
      match_states (State stk f sp pc rs m)
                   (State stk' (transf_function f) sp (renum_pc (pnum f) pc) rs m)
  | match_returnstates: forall stk v m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk v m)
                   (Returnstate stk' v m).

Inductive match_call: RTL.state -> RTL.state -> Prop :=
  | match_callstates: forall stk f args m stk' f'
        (STACKS: list_forall2 match_frames stk stk')
        (FUN: fundef_weak_lsim Language_RTL Language_RTL id ge tge f f'),
      match_call (Callstate stk f args m)
                 (Callstate stk' f' args m).

Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', RTL.step tge S1' t S2' /\ (match_states S2 S2' \/ match_call S2 S2').
Proof.
  induction 1; intros S1' MS; inv MS; try TR_AT.
(* nop *)
  econstructor; split. eapply exec_Inop; eauto. 
  left. constructor; auto. eapply reach_succ; eauto. simpl; auto. 
(* op *)
  econstructor; split.
  eapply exec_Iop; eauto.
  instantiate (1 := v). rewrite <- H0. apply eval_operation_preserved. apply symbols_preserved. auto. 
  left. constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* load *)
  econstructor; split.
  assert (eval_addressing tge sp addr rs ## args = Some a).
  rewrite <- H0. apply eval_addressing_preserved. apply symbols_preserved. auto. 
  eapply exec_Iload; eauto.
  left. constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* store *)
  econstructor; split.
  assert (eval_addressing tge sp addr rs ## args = Some a).
  rewrite <- H0. apply eval_addressing_preserved. apply symbols_preserved. auto. 
  eapply exec_Istore; eauto.
  left. constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* call *)
  exploit find_function_translated_Renumber; eauto. intros [tf [Htf FIND]].
  econstructor; split.
  eapply exec_Icall; eauto. eapply sig_preserved. eauto.
  right. constructor; auto. constructor; auto. constructor. eapply reach_succ; eauto. simpl; auto.
(* tailcall *)
  exploit find_function_translated_Renumber; eauto. intros [tf [Htf FIND]].
  econstructor; split.
  eapply exec_Itailcall; eauto. eapply sig_preserved. eauto.
  right. constructor; auto.
(* builtin *)
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
    eapply external_call_symbols_preserved; eauto.
    apply symbols_preserved. auto. apply varinfo_preserved. auto.
  left. constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* cond *)
  econstructor; split.
  eapply exec_Icond; eauto. 
  replace (if b then renum_pc (pnum f) ifso else renum_pc (pnum f) ifnot)
     with (renum_pc (pnum f) (if b then ifso else ifnot)).
  left. constructor; auto. eapply reach_succ; eauto. simpl. destruct b; auto. 
  destruct b; auto.
(* jumptbl *)
  econstructor; split.
  eapply exec_Ijumptable; eauto. rewrite list_nth_z_map. rewrite H1. simpl; eauto. 
  left. constructor; auto. eapply reach_succ; eauto. simpl. eapply list_nth_z_in; eauto. 
(* return *)
  econstructor; split.
  eapply exec_Ireturn; eauto. 
  left. constructor; auto.
(* (* internal function *) *)
(*   simpl. econstructor; split. *)
(*   eapply exec_function_internal; eauto.  *)
(*   constructor; auto. unfold reach. constructor.  *)
(* (* external function *) *)
(*   econstructor; split. *)
(*   eapply exec_function_external; eauto. *)
(*     eapply external_call_symbols_preserved; eauto. *)
(*     apply symbols_preserved. auto. apply varinfo_preserved. auto. *)
(*   constructor; auto. *)
(* return *)
  inv STACKS. inv H1.
  econstructor; split. 
  eapply exec_return; eauto. 
  left. constructor; auto.
Qed.

Lemma transf_initial_states:
  forall S1, RTL.initial_state fprog S1 ->
  exists S2, RTL.initial_state ftprog S2 /\ match_call S1 S2.
Proof.
  intros. inversion H. 
  exploit funct_ptr_translated; eauto. intros [tf [A B]].
  exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
  eapply (@program_lsim_init_mem_match Language_RTL Language_RTL); try apply transf_efT_sigT; eauto.
  replace (AST.prog_main ftprog) with (AST.prog_main fprog).
  erewrite symbols_preserved; eauto.
  destruct Hfsim as [_ Hmain]. unfold fundef in *. simpl in *. rewrite <- Hmain. auto.
  rewrite <- H3. eapply sig_preserved; eauto.
  constructor. constructor. auto.
Qed.

Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> RTL.final_state S2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. constructor.
Qed.

Inductive match_states_ext st tst: Prop :=
| match_states_ext_intro
    (Hmatch: match_states st tst)
    (Hsrc: ValueAnalysis_linker.sound_state_ext fprog st)
    (Htgt: ValueAnalysis_linker.sound_state_ext ftprog tst)
.

End FUTURE.

(* memory relation *)

Inductive mrelT_sem (mrel:unit) (fprog ftprog:program) (i:WF.t) (s1 s2:state): Prop :=
| mrelT_sem_intro
    (MEASURE: i = WF.elt)
    (MS: match_states s1 s2 \/ match_call fprog ftprog s1 s2)
.

Definition mrelT_ops: mrelT_opsT unit :=
  mkmrelT_opsT
    mrelT_sem
    (fun _ v1 v2 => v1 = v2)
    (fun _ _ => True)
    (fun _ _ => True).

Lemma mrelT_ops_equal_list mrel v1 v2:
  v1 = v2 <-> list_forall2 (mrelT_ops.(sem_value) mrel) v1 v2.
Proof.
  revert v2.
  induction v1; intros; constructor; intro H; inv H; try constructor; simpl; auto.
  - apply IHv1. auto.
  - f_equal; auto. apply IHv1. auto.
Qed.

Program Definition mrelT_props: mrelT_propsT mrelT_ops := mkmrelT_propsT _ _ _ _ _ _ _.
Next Obligation. repeat constructor. Qed.
Next Obligation. repeat constructor. Qed.
Next Obligation.
  exploit transf_initial_states; eauto. intros [s2' [Hs2' Hinit]].
  generalize (initial_state_unique Hs2' H2). intro. subst.
  exists tt. exists WF.elt. constructor; auto.
Qed.
Next Obligation.
  apply (mrelT_ops_equal_list mrel args1 args2) in Hargs.
  inv Hs0. inv Hmrel. destruct MS as [MS|MS]; inv MS.

(* external function *)
  exists tt. exists WF.elt. eexists. eexists. eexists. split; [eauto|]. split.
  eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto.
    apply symbols_preserved. auto. apply varinfo_preserved. auto.
  repeat (constructor; auto).
Qed.

Section STATE_LSIM.
  
Variable (fprog ftprog:program).
Hypothesis (Hfsim: @program_weak_lsim Language_RTL Language_RTL id (@Errors.OK _) transf_V
                                      fprog ftprog).

Hypothesis (Hfprog: program_linkeq Language_RTL prog fprog).
Hypothesis (Hftprog: program_linkeq Language_RTL tprog ftprog).

Lemma match_states_state_lsim es es' eF F i s1 s1'
      (MS: match_states_ext fprog ftprog s1 s1'):
  state_lsim mrelT_ops fprog ftprog es es' eF F i s1 s1'.
Proof.
  revert F i s1 s1' MS. pcofix CIH. intros F i s1 s1' MS. pfold.
  inversion MS. destruct (classic (exists r, final_state s1 r)).
  { destruct H as [rval Hrval]. eapply _state_lsim_term; eauto.
    eapply transf_final_states; eauto.
  }
  constructor; auto.
  { repeat intro. apply H. exists r0. auto. }
  intros. exploit step_simulation; eauto. simpl.
  intros [s2' [Hs2' Hmatch2]].
  exists WF.elt. exists s2'. exists tt.
  split; [destruct Hmatch2; left; apply plus_one; auto|].
  split; auto. split; [constructor; auto|].
  destruct Hmatch2 as [Hmatch2|Hmatch2].
  - apply _state_lsim_or_csim_lsim. right. apply CIH.
    constructor; auto.
    + eapply ValueAnalysis_linker.sound_past_step; eauto.
    + eapply ValueAnalysis_linker.sound_past_step; eauto.
  - inversion Hmatch2. subst. eapply _state_lsim_or_csim_csim; eauto.
    + apply (mrelT_ops_equal_list tt). auto.
    + constructor; auto.
    + intros. subst. inversion Hst2_mem. subst. destruct MS0 as [MS0|MS0]; [|inv MS0].
      right. apply CIH. constructor; auto.
Qed.

Lemma transf_function_lsim f:
  function_lsim mrelT_ops fprog ftprog f (transf_function f).
Proof.
  constructor. intros. pfold. constructor; subst; auto.
  { intros ? Hfinal. inv Hfinal. }
  intros. inversion Hst2_src. subst.
  inv Hmrel_entry. destruct MS as [MS|MS]; inversion MS; subst.

(* internal function *)
  exists WF.elt. eexists. exists tt. split.
  left. apply plus_one.
  eapply exec_function_internal; eauto.
  simpl. split; [auto|].
  cut (match_states
         (State cs_entry_src f (Values.Vptr stk Integers.Int.zero)
                (fn_entrypoint f) (init_regs args_tgt (fn_params f)) m')
         (State cs_entry_tgt (transf_function f)
                (Values.Vptr stk Integers.Int.zero)
                (renum_pc (postorder (successors_map f) (fn_entrypoint f))
                          (fn_entrypoint f)) (init_regs args_tgt (fn_params f)) m')).
  { intro MS2. split; [constructor; eauto|].
    constructor. left. apply match_states_state_lsim. constructor; auto.
    - eapply ValueAnalysis_linker.sound_past_step; eauto.
    - eapply ValueAnalysis_linker.sound_past_step; eauto.
      apply (exec_function_internal _ cs_entry_tgt (transf_function f)). auto.
  }
  constructor; auto. unfold reach. constructor. 
Qed.

End STATE_LSIM.

Lemma Renumber_program_lsim:
  @program_lsim Language_RTL Language_RTL id (@Errors.OK _) transf_V
                (function_lsim mrelT_ops)
                prog tprog.
Proof.
  generalize transf_function_lsim.
  destruct prog as [defs main]. simpl in *.
  unfold transf_program, AST.transform_program in TRANSF.
  inv TRANSF. intro Hlsim. constructor; simpl; auto.
  revert Hlsim.
  generalize defs at 1 2 3 4 as fdefs. revert defs.
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
