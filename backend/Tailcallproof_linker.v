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
Require Import Tailcall.
Require Import Tailcallproof.
Require Import RTL_linker ValueAnalysis_linker.
Require Import WFType paco.

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

Inductive match_stackframes: list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes nil nil
  | match_stackframes_normal: forall stk stk' res sp pc rs rs' f,
      match_stackframes stk stk' ->
      regset_lessdef rs rs' ->
      match_stackframes
        (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
        (Stackframe res (transf_function f) (Vptr sp Int.zero) pc rs' :: stk')
  | match_stackframes_tail: forall stk stk' res sp pc rs f,
      match_stackframes stk stk' ->
      is_return_spec f pc res ->
      f.(fn_stacksize) = 0 ->
      match_stackframes
        (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
        stk'.

Inductive match_states: state -> state -> Prop :=
  | match_states_normal:
      forall s sp pc rs m s' rs' m' f
             (STACKS: match_stackframes s s')
             (RLD: regset_lessdef rs rs')
             (MLD: Mem.extends m m'),
      match_states (State s f (Vptr sp Int.zero) pc rs m)
                   (State s' (transf_function f) (Vptr sp Int.zero) pc rs' m')
  | match_states_return:
      forall s v m s' v' m',
      match_stackframes s s' ->
      Val.lessdef v v' ->
      Mem.extends m m' ->
      match_states (Returnstate s v m)
                   (Returnstate s' v' m')
  | match_states_interm:
      forall s sp pc rs m s' m' f r v'
             (STACKS: match_stackframes s s')
             (MLD: Mem.extends m m'),
      is_return_spec f pc r ->
      f.(fn_stacksize) = 0 ->
      Val.lessdef (rs#r) v' ->
      match_states (State s f (Vptr sp Int.zero) pc rs m)
                   (Returnstate s' v' m').

Inductive match_call: state -> state -> Prop :=
  | match_states_call:
      forall s f args m s' f' args' m',
      match_stackframes s s' ->
      globfun_weak_lsim Language_RTL Language_RTL transf_sigT ge tge f f' ->
      Val.lessdef_list args args' ->
      Mem.extends m m' ->
      match_call (Callstate s f args m)
                 (Callstate s' f' args' m').

Ltac TransfInstr :=
  match goal with
  | H: (PTree.get _ (fn_code _) = _) |- _ =>
      destruct (transf_instr_lookup _ _ _ H) as [i' [TINSTR TSPEC]]; inv TSPEC
  end.

Ltac EliminatedInstr :=
  match goal with
  | H: (is_return_spec _ _ _) |- _ => inv H; try congruence
  | _ => idtac
  end.

Lemma transf_step_correct:
  forall s1 t s2, step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  (exists s2', step tge s1' t s2' /\ (match_states s2 s2' \/ match_call s2 s2')) \/
  (measure s2 < measure s1 /\ t = E0 /\ (match_states s2 s1' \/ match_call s2 s1'))%nat.
Proof.
  induction 1; intros; inv MS; EliminatedInstr.

(* nop *)
  TransfInstr. left. econstructor; split. 
  eapply exec_Inop; eauto. left. constructor; auto.
(* eliminated nop *)
  assert (s0 = pc') by congruence. subst s0.
  right. split. simpl. omega. split. auto. 
  left. econstructor; eauto. 

(* op *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regset_get_list; auto. 
  exploit eval_operation_lessdef; eauto. 
  intros [v' [EVAL' VLD]]. 
  left. exists (State s' (transf_function f) (Vptr sp0 Int.zero) pc' (rs'#res <- v') m'); split.
  eapply exec_Iop; eauto.  rewrite <- EVAL'.
  apply eval_operation_preserved. apply symbols_preserved. auto.
  left. econstructor; eauto. apply regset_set; auto.
(* eliminated move *)
  rewrite H1 in H. clear H1. inv H. 
  right. split. simpl. omega. split. auto.
  left. econstructor; eauto. simpl in H0. rewrite PMap.gss. congruence. 

(* load *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regset_get_list; auto. 
  exploit eval_addressing_lessdef; eauto. 
  intros [a' [ADDR' ALD]].
  exploit Mem.loadv_extends; eauto. 
  intros [v' [LOAD' VLD]].
  left. exists (State s' (transf_function f) (Vptr sp0 Int.zero) pc' (rs'#dst <- v') m'); split.
  eapply exec_Iload with (a := a'). eauto.  rewrite <- ADDR'.
  apply eval_addressing_preserved. apply symbols_preserved. auto. eauto.
  left. econstructor; eauto. apply regset_set; auto.

(* store *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regset_get_list; auto. 
  exploit eval_addressing_lessdef; eauto. 
  intros [a' [ADDR' ALD]].
  exploit Mem.storev_extends. 2: eexact H1. eauto. eauto. apply RLD.  
  intros [m'1 [STORE' MLD']].
  left. exists (State s' (transf_function f) (Vptr sp0 Int.zero) pc' rs' m'1); split.
  eapply exec_Istore with (a := a'). eauto.  rewrite <- ADDR'.
  apply eval_addressing_preserved. apply symbols_preserved. auto. eauto.
  destruct a; simpl in H1; try discriminate.
  left. econstructor; eauto.

(* call *)
  exploit find_function_translated_Tailcall; eauto. intros [fd' [Hfd' FIND']].  
  TransfInstr.
(* call turned tailcall *)
  assert ({ m'' | Mem.free m' sp0 0 (fn_stacksize (transf_function f)) = Some m''}).
    apply Mem.range_perm_free. rewrite stacksize_preserved. rewrite H7. 
    red; intros; omegaContradiction.
  destruct X as [m'' FREE].
  left. exists (Callstate s' fd' (rs'##args) m''); split.
  eapply exec_Itailcall; eauto. eapply sig_preserved. eauto. auto.
  right. constructor; auto. eapply match_stackframes_tail; eauto. apply regset_get_list; auto.
  eapply Mem.free_right_extends; eauto.
  rewrite stacksize_preserved. rewrite H7. intros. omegaContradiction.
(* call that remains a call *)
  left. exists (Callstate (Stackframe res (transf_function f) (Vptr sp0 Int.zero) pc' rs' :: s')
                          fd' (rs'##args) m'); split.
  eapply exec_Icall; eauto. eapply sig_preserved. eauto. auto. 
  right. constructor; auto. constructor; auto. apply regset_get_list; auto.

(* tailcall *) 
  exploit find_function_translated_Tailcall; eauto. intros [fd' [Hfd' FIND']].
  exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
  TransfInstr.
  left. exists (Callstate s' fd' (rs'##args) m'1); split.
  eapply exec_Itailcall; eauto. eapply sig_preserved. eauto. auto.
  rewrite stacksize_preserved; auto.
  right. constructor; auto.  apply regset_get_list; auto.

(* builtin *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regset_get_list; auto. 
  exploit external_call_mem_extends; eauto.
  intros [v' [m'1 [A [B [C D]]]]].
  left. exists (State s' (transf_function f) (Vptr sp0 Int.zero) pc' (rs'#res <- v') m'1); split.
  eapply exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved; eauto.
  apply symbols_preserved. auto. apply varinfo_preserved. auto.
  left. econstructor; eauto. apply regset_set; auto.

(* cond *)
  TransfInstr. 
  left. exists (State s' (transf_function f) (Vptr sp0 Int.zero) (if b then ifso else ifnot) rs' m'); split.
  eapply exec_Icond; eauto.
  apply eval_condition_lessdef with (rs##args) m; auto. apply regset_get_list; auto.
  left. constructor; auto. 

(* jumptable *)
  TransfInstr. 
  left. exists (State s' (transf_function f) (Vptr sp0 Int.zero) pc' rs' m'); split.
  eapply exec_Ijumptable; eauto.
  generalize (RLD arg). rewrite H0. intro. inv H2. auto.
  left. constructor; auto. 

(* return *)
  exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
  TransfInstr.
  left. exists (Returnstate s' (regmap_optget or Vundef rs') m'1); split.
  apply exec_Ireturn; auto. rewrite stacksize_preserved; auto.
  left. constructor. auto.
  destruct or; simpl. apply RLD. constructor.
  auto.

(* eliminated return None *)
  assert (or = None) by congruence. subst or. 
  right. split. simpl. omega. split. auto. 
  left.  constructor. auto.
  simpl. constructor.
  eapply Mem.free_left_extends; eauto. 

(* eliminated return Some *)
  assert (or = Some r) by congruence. subst or.
  right. split. simpl. omega. split. auto.
  left. constructor. auto.
  simpl. auto.
  eapply Mem.free_left_extends; eauto.

(* (* internal call *) *)
(*   exploit Mem.alloc_extends; eauto. *)
(*     instantiate (1 := 0). omega. *)
(*     instantiate (1 := fn_stacksize f). omega. *)
(*   intros [m'1 [ALLOC EXT]]. *)
(*   assert (fn_stacksize (transf_function f) = fn_stacksize f /\ *)
(*           fn_entrypoint (transf_function f) = fn_entrypoint f /\ *)
(*           fn_params (transf_function f) = fn_params f). *)
(*     unfold transf_function. destruct (zeq (fn_stacksize f) 0 && eliminate_tailcalls tt); auto.  *)
(*   destruct H0 as [EQ1 [EQ2 EQ3]].  *)
(*   left. econstructor; split. *)
(*   simpl. eapply exec_function_internal; eauto. rewrite EQ1; eauto. *)
(*   rewrite EQ2. rewrite EQ3. constructor; auto. *)
(*   apply regset_init_regs. auto.  *)

(* (* external call *) *)
(*   exploit external_call_mem_extends; eauto. *)
(*   intros [res' [m2' [A [B [C D]]]]]. *)
(*   left. exists (Returnstate s' res' m2'); split. *)
(*   simpl. econstructor; eauto. *)
(*   eapply external_call_symbols_preserved; eauto. *)
(*   exact symbols_preserved. exact varinfo_preserved. *)
(*   constructor; auto.  *)

(* returnstate *)
  inv H2. 
(* synchronous return in both programs *)
  left. econstructor; split. 
  apply exec_return. 
  left. constructor; auto. apply regset_set; auto. 
(* return instr in source program, eliminated because of tailcall *)
  right. split. unfold measure. simpl length. 
  change (S (length s) * (niter + 2))%nat
   with ((niter + 2) + (length s) * (niter + 2))%nat. 
  generalize (return_measure_bounds (fn_code f) pc). omega.  
  split. auto. 
  left. econstructor; eauto.
  rewrite Regmap.gss. auto. 
Qed.

Lemma transf_initial_states:
  forall st1, initial_state fprog st1 ->
  exists st2, initial_state ftprog st2 /\ match_call st1 st2.
Proof.
  intros. inversion H. 
  exploit funct_ptr_translated; eauto. intros [tf [A B]].
  exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
  eapply (@program_lsim_init_mem_match Language_RTL Language_RTL); try apply transf_efT_sigT; eauto.
  replace (prog_main ftprog) with (prog_main fprog).
  erewrite symbols_preserved; eauto.
  destruct Hfsim as [_ Hmain]. unfold fundef in *. simpl in *. rewrite <- Hmain. auto.
  rewrite <- H3. eapply sig_preserved; eauto.
  constructor. constructor. auto. auto. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H5. inv H3. constructor. 
Qed.

Inductive match_states_ext st tst: Prop :=
| match_states_ext_intro
    (Hsrc: sound_state_ext fprog st)
    (Htgt: sound_state_ext ftprog tst)
    (Hmatch: match_states st tst)
.

End FUTURE.

(* memory relation *)

Inductive mrelT_sem (mrel:unit) (fprog ftprog:program) (i:WF.t) (s1 s2:state): Prop :=
| mrelT_sem_intro
    (MEASURE: i = WF.from_nat (measure s1))
    (Hsrc: sound_state_ext fprog s1)
    (Htgt: sound_state_ext ftprog s2)
    (MS: match_states s1 s2 \/ match_call fprog ftprog s1 s2)
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
  exploit transf_initial_states; eauto. intros [s2' [Hs2' Hinit]].
  generalize (initial_state_unique Hs2' H2). intro. subst.
  exists tt. eexists. econstructor; eauto.
  - apply sound_initial. auto.
  - apply sound_initial. auto.
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

Lemma match_states_state_lsim es es' eF F s1 s1'
      (MS: match_states_ext fprog ftprog s1 s1'):
  @state_lsim Language_ext_RTL Language_ext_RTL transf_sigT _
              mrelT_ops fprog ftprog es es' eF F (WF.from_nat (measure s1)) s1 s1'.
Proof.
  revert F s1 s1' MS. pcofix CIH. intros F s1 s1' MS. pfold.
  inversion MS. destruct (classic (exists r, final_state s1 r)).
  { destruct H as [rval Hrval]. eapply _state_lsim_term; eauto.
    - apply final_state_equiv. eauto.
    - apply final_state_equiv. eapply transf_final_states; eauto.
  }
  constructor; auto.
  { repeat intro. apply H. exists r0. apply final_state_equiv. auto. }
  intros. exploit transf_step_correct; eauto. simpl.
  intros [[s2' [Hs2' Hmatch2]]|[Hmeasure [Hevt Hmatch2]]].
  { eexists. exists s2'. exists tt.
    split; [destruct Hmatch2; left; apply plus_one; auto|].
    split; auto. split; [constructor; auto|].
    { eapply sound_past_step; eauto. }
    { eapply sound_past_step; eauto. }
    destruct Hmatch2 as [Hmatch2|Hmatch2].
    - apply _state_lsim_or_csim_lsim. right. apply CIH.
      constructor; auto.
      + eapply sound_past_step; eauto.
      + eapply sound_past_step; eauto.
    - inversion Hmatch2. subst. eapply _state_lsim_or_csim_csim; eauto.
      + apply (mrelT_ops_lessdef_list tt). auto.
      + constructor; auto.
        * eapply sound_past_step; eauto.
        * eapply sound_past_step; eauto.
      + intros. subst. inversion Hst2_mem. subst. destruct MS0 as [MS0|MS0]; [|inv MS0].
        right. apply CIH. constructor; auto.
  }
  { eexists. exists s1'. exists tt.
    split; [right; split; [subst; econstructor|constructor; eauto]|].
    split; [auto|].
    split; [constructor; auto|].
    { eapply sound_past_step; eauto. }
    destruct Hmatch2 as [Hmatch2|Hmatch2].
    - apply _state_lsim_or_csim_lsim. right. apply CIH.
      constructor; auto.
      eapply sound_past_step; eauto.
    - inversion Hmatch2. subst. eapply _state_lsim_or_csim_csim; eauto.
      + apply (mrelT_ops_lessdef_list tt). auto.
      + constructor; auto.
        eapply sound_past_step; eauto.
      + intros. subst. inversion Hst2_mem. subst. destruct MS0 as [MS0|MS0]; [|inv MS0].
        right. apply CIH. constructor; auto.
  }
Qed.

Lemma transf_function_lsim f:
  @function_lsim Language_ext_RTL Language_ext_RTL transf_sigT _
                 mrelT_ops fprog ftprog f (transf_function f).
Proof.
  constructor. intros. pfold. constructor; subst; auto.
  { intros ? Hfinal. apply final_state_equiv in Hfinal. inv Hfinal. }
  intros. destruct fd_src; inv Hfd_src. destruct fd_tgt; inv Hfd_tgt. inversion Hst2_src. subst.
  inv Hmrel_entry. destruct MS as [MS|MS]; inversion MS; subst.

  (* internal call *)
  exploit Mem.alloc_extends; eauto.
    instantiate (1 := 0). omega.
    instantiate (1 := fn_stacksize f). omega.
  intros [m'1 [ALLOC EXT]].
  assert (fn_stacksize (transf_function f) = fn_stacksize f /\
          fn_entrypoint (transf_function f) = fn_entrypoint f /\
          fn_params (transf_function f) = fn_params f).
    unfold transf_function. destruct (zeq (fn_stacksize f) 0 && Compopts.eliminate_tailcalls tt); auto.
  destruct H as [EQ1 [EQ2 EQ3]].
  eexists. eexists. exists tt. split.
  left. apply plus_one. eapply exec_function_internal; eauto. rewrite EQ1; eauto.
  simpl. split; [auto|].
  cut (match_states
         (State es_src f (Vptr stk Int.zero) (fn_entrypoint f)
                (init_regs args_src (fn_params f)) m')
         (State es_tgt (transf_function f) (Vptr stk Int.zero)
                (fn_entrypoint (transf_function f))
                (init_regs args_tgt (fn_params (transf_function f))) m'1)).
  { intro MS2. split; [constructor; eauto|].
    - eapply sound_past_step; eauto.
    - eapply sound_past_step; eauto. constructor; auto. rewrite EQ1. auto.
    - constructor. left. apply match_states_state_lsim. constructor; auto.
      + eapply sound_past_step; eauto.
      + eapply sound_past_step; eauto. constructor; auto. rewrite EQ1. auto.
  }
  rewrite EQ2. rewrite EQ3. constructor; auto.
  apply regset_init_regs. auto.
Qed.

End STATE_LSIM.

Lemma Tailcall_program_lsim:
  @program_lsim Language_RTL Language_RTL transf_sigT transf_efT transf_vT
                (@function_lsim Language_ext_RTL Language_ext_RTL transf_sigT _ mrelT_ops)
                prog tprog.
Proof.
  generalize transf_function_lsim.
  destruct prog as [defs main]. simpl in *.
  unfold transf_program, transform_program in TRANSF.
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
      unfold transf_function. destruct (zeq (fn_stacksize f) 0 && Compopts.eliminate_tailcalls tt); simpl; auto.
    + eapply globfun_lsim_intro; eauto; simpl; auto.
  - constructor; simpl in *; try apply IHdefs; auto.
    split; auto. apply (@globdef_lsim_var Language_RTL Language_RTL).
    repeat constructor. destruct v; auto.
Qed.

End PRESERVATION.
