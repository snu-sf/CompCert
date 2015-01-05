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
Require Import CSE.
Require Import CSEproof.
Require Import RTL_linker ValueAnalysis_linker.
Require Import WFType paco.

Set Implicit Arguments.

Section PRESERVATION.

Variable (prog tprog: program).
Hypothesis TRANSF: transf_program prog = OK tprog.

Section FUTURE.

Variable (fprog ftprog:program).
Hypothesis (Hfsim: @program_weak_lsim Language_RTL Language_RTL transf_sigT transf_efT transf_vT
                                      fprog ftprog).

Hypothesis (Hfprog: program_linkeq Language_RTL prog fprog).
Hypothesis (Hftprog: program_linkeq Language_RTL tprog ftprog).

Let globfun_weak_lsim :=
  @globfun_lsim Language_RTL Language_RTL transf_sigT transf_efT
                (fun _ _ _ _ => True)
                fprog ftprog.

Let ge := Genv.globalenv fprog.
Let tge := Genv.globalenv ftprog.

Inductive match_stackframes: list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes nil nil
  | match_stackframes_cons:
      forall res sp pc rs f approx s rs' s' rm
           (RM: PTree_le rm (romem_for_program fprog))
           (ANALYZE: analyze f (vanalyze rm f) = Some approx)
           (SAT: forall v m, exists valu, numbering_holds valu ge sp (rs#res <- v) m approx!!pc)
           (RLD: regs_lessdef rs rs')
           (STACKS: match_stackframes s s'),
    match_stackframes
      (Stackframe res f sp pc rs :: s)
      (Stackframe res (transf_function' f approx) sp pc rs' :: s').

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m s' rs' m' f approx rm
             (RM: PTree_le rm (romem_for_program fprog))
             (ANALYZE: analyze f (vanalyze rm f) = Some approx)
             (SAT: exists valu, numbering_holds valu ge sp rs m approx!!pc)
             (RLD: regs_lessdef rs rs')
             (MEXT: Mem.extends m m')
             (STACKS: match_stackframes s s'),
      match_states (State s f sp pc rs m)
                   (State s' (transf_function' f approx) sp pc rs' m')
  | match_states_return:
      forall s s' v v' m m',
      match_stackframes s s' ->
      Val.lessdef v v' ->
      Mem.extends m m' ->
      match_states (Returnstate s v m)
                   (Returnstate s' v' m').

Inductive match_call: state -> state -> Prop :=
  | match_states_call:
      forall s f tf args m s' args' m',
      match_stackframes s s' ->
      fundef_weak_lsim Language_RTL Language_RTL transf_sigT ge tge f tf ->
      Val.lessdef_list args args' ->
      Mem.extends m m' ->
      match_call (Callstate s f args m)
                 (Callstate s' tf args' m').

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc ?c = Some ?instr), f: function, approx: PMap.t numbering |- _ =>
      cut ((transf_function' f approx).(fn_code)!pc = Some(transf_instr approx!!pc instr));
      [ simpl transf_instr
      | unfold transf_function', transf_code; simpl; rewrite PTree.gmap; 
        unfold option_map; rewrite H1; reflexivity ]
  end.

Lemma transf_step_correct:
  forall s1 t s2, step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1') (SOUND: sound_state_ext fprog s1),
  exists s2', step tge s1' t s2' /\ (match_states s2 s2' \/ match_call s2 s2').
Proof.
  induction 1; intros; inv MS; try (TransfInstr; intro C).

  (* Inop *)
- econstructor; split.
  eapply exec_Inop; eauto.
  left. econstructor; eauto. 
  eapply analysis_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H; auto.

  (* Iop *)
- destruct (is_trivial_op op) eqn:TRIV.
+ (* unchanged *)
  exploit eval_operation_lessdef. eapply regs_lessdef_regs; eauto. eauto. eauto.
  intros [v' [A B]].
  econstructor; split.
  eapply exec_Iop with (v := v'); eauto.
  rewrite <- A. apply eval_operation_preserved. apply symbols_preserved. eauto.
  left. econstructor; eauto. 
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H. 
  destruct SAT as [valu NH]. eapply add_op_holds; eauto.
  apply set_reg_lessdef; auto.
+ (* possibly optimized *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (find_rhs n1 (Op op vl)) as [r|] eqn:?.
* (* replaced by move *)
  exploit find_rhs_sound; eauto. intros (v' & EV & LD). 
  assert (v' = v) by (inv EV; congruence). subst v'.
  econstructor; split.
  eapply exec_Iop; eauto. simpl; eauto.
  left. econstructor; eauto. 
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H. 
  eapply add_op_holds; eauto. 
  apply set_reg_lessdef; auto.
  eapply Val.lessdef_trans; eauto.
* (* possibly simplified *)
  destruct (reduce operation combine_op n1 op args vl) as [op' args'] eqn:?.
  assert (RES: eval_operation ge sp op' rs##args' m = Some v).
    eapply reduce_sound with (sem := fun op vl => eval_operation ge sp op vl m); eauto. 
    intros; eapply combine_op_sound; eauto.
  exploit eval_operation_lessdef. eapply regs_lessdef_regs; eauto. eauto. eauto.
  intros [v' [A B]].
  econstructor; split.
  eapply exec_Iop with (v := v'); eauto.   
  rewrite <- A. apply eval_operation_preserved. apply symbols_preserved. eauto.
  left. econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H. 
  eapply add_op_holds; eauto. 
  apply set_reg_lessdef; auto. 

- (* Iload *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (find_rhs n1 (Load chunk addr vl)) as [r|] eqn:?.
+ (* replaced by move *)
  exploit find_rhs_sound; eauto. intros (v' & EV & LD). 
  assert (v' = v) by (inv EV; congruence). subst v'.
  econstructor; split.
  eapply exec_Iop; eauto. simpl; eauto.
  left. econstructor; eauto. 
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H. 
  eapply add_load_holds; eauto. 
  apply set_reg_lessdef; auto. eapply Val.lessdef_trans; eauto.
+ (* load is preserved, but addressing is possibly simplified *)
  destruct (reduce addressing combine_addr n1 addr args vl) as [addr' args'] eqn:?.
  assert (ADDR: eval_addressing ge sp addr' rs##args' = Some a).
  { eapply reduce_sound with (sem := fun addr vl => eval_addressing ge sp addr vl); eauto. 
    intros; eapply combine_addr_sound; eauto. }
  exploit eval_addressing_lessdef. apply regs_lessdef_regs; eauto. eexact ADDR.
  intros [a' [A B]].
  assert (ADDR': eval_addressing tge sp addr' rs'##args' = Some a').
  { rewrite <- A. apply eval_addressing_preserved. apply symbols_preserved. auto. }
  exploit Mem.loadv_extends; eauto. 
  intros [v' [X Y]].
  econstructor; split.
  eapply exec_Iload; eauto.
  left. econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. 
  eapply add_load_holds; eauto.
  apply set_reg_lessdef; auto.

- (* Istore *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (reduce addressing combine_addr n1 addr args vl) as [addr' args'] eqn:?.
  assert (ADDR: eval_addressing ge sp addr' rs##args' = Some a).
  { eapply reduce_sound with (sem := fun addr vl => eval_addressing ge sp addr vl); eauto. 
    intros; eapply combine_addr_sound; eauto. }
  exploit eval_addressing_lessdef. apply regs_lessdef_regs; eauto. eexact ADDR.
  intros [a' [A B]].
  assert (ADDR': eval_addressing tge sp addr' rs'##args' = Some a').
  { rewrite <- A. apply eval_addressing_preserved. apply symbols_preserved. auto. }
  exploit Mem.storev_extends; eauto. intros [m'' [X Y]].
  econstructor; split.
  eapply exec_Istore; eauto.
  left. econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H.
  inv SOUND. specialize (Hsound _ RM). inv Hsound.
  eapply add_store_result_hold; eauto. 
  eapply kill_loads_after_store_holds; eauto.

- (* Icall *)
  exploit find_function_translated_CSE; eauto. intros [tf [FIND' TRANSF']]. 
  econstructor; split.
  eapply exec_Icall; eauto.
  eapply sig_preserved; eauto.
  right. econstructor; eauto. 
  econstructor; eauto. 
  intros. eapply analysis_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. 
  exists (fun _ => Vundef); apply empty_numbering_holds.
  apply regs_lessdef_regs; auto.

- (* Itailcall *)
  exploit find_function_translated_CSE; eauto. intros [tf [FIND' TRANSF']]. 
  exploit Mem.free_parallel_extends; eauto. intros [m'' [A B]].
  econstructor; split.
  eapply exec_Itailcall; eauto.
  eapply sig_preserved; eauto.
  right. econstructor; eauto. 
  apply regs_lessdef_regs; auto.

- (* Ibuiltin *)
  exploit external_call_mem_extends; eauto.
  instantiate (1 := rs'##args). apply regs_lessdef_regs; auto.
  intros (v' & m1' & P & Q & R & S).
  econstructor; split.
  eapply exec_Ibuiltin; eauto. 
  eapply external_call_symbols_preserved; eauto.
  apply symbols_preserved. auto. apply varinfo_preserved. auto.
  left. econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
* unfold transfer; rewrite H.
  destruct SAT as [valu NH].
  assert (CASE1: exists valu, numbering_holds valu ge sp (rs#res <- v) m' empty_numbering).
  { exists valu; apply empty_numbering_holds. }
  assert (CASE2: m' = m -> exists valu, numbering_holds valu ge sp (rs#res <- v) m' (set_unknown approx#pc res)).
  { intros. rewrite H1. exists valu. apply set_unknown_holds; auto. }
  assert (CASE3: exists valu, numbering_holds valu ge sp (rs#res <- v) m'
                         (set_unknown (kill_all_loads approx#pc) res)).
  { exists valu. apply set_unknown_holds. eapply kill_all_loads_hold; eauto. }
  destruct ef.
  + apply CASE1.
  + apply CASE3. 
  + apply CASE2; inv H0; auto.
  + apply CASE3.
  + apply CASE2; inv H0; auto. 
  + apply CASE3; auto.
  + apply CASE1.
  + apply CASE1.
  + destruct args as [ | rdst args]; auto.
    destruct args as [ | rsrc args]; auto. 
    destruct args; auto.
    simpl in H0. inv H0. 
    exists valu. 
    apply set_unknown_holds. 
    inv SOUND. specialize (Hsound _ RM). inv Hsound. eapply add_memcpy_holds; eauto. 
    eapply kill_loads_after_storebytes_holds; eauto. 
    eapply Mem.loadbytes_length; eauto. 
    simpl. apply Ple_refl. 
  + apply CASE2; inv H0; auto.
  + apply CASE2; inv H0; auto.
  + apply CASE1.
* apply set_reg_lessdef; auto.

- (* Icond *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  elim SAT; intros valu1 NH1.
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (reduce condition combine_cond n1 cond args vl) as [cond' args'] eqn:?.
  assert (RES: eval_condition cond' rs##args' m = Some b).
  { eapply reduce_sound with (sem := fun cond vl => eval_condition cond vl m); eauto. 
    intros; eapply combine_cond_sound; eauto. }
  econstructor; split.
  eapply exec_Icond; eauto. 
  eapply eval_condition_lessdef; eauto. apply regs_lessdef_regs; auto.
  left. econstructor; eauto.
  destruct b; eapply analysis_correct_1; eauto; simpl; auto;
  unfold transfer; rewrite H; auto.

- (* Ijumptable *)
  generalize (RLD arg); rewrite H0; intro LD; inv LD.
  econstructor; split.
  eapply exec_Ijumptable; eauto. 
  left. econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl. eapply list_nth_z_in; eauto.
  unfold transfer; rewrite H; auto.

- (* Ireturn *)
  exploit Mem.free_parallel_extends; eauto. intros [m'' [A B]].
  econstructor; split.
  eapply exec_Ireturn; eauto.
  left. econstructor; eauto.
  destruct or; simpl; auto. 

(* - (* internal function *) *)
(*   monadInv H6. unfold transf_function in EQ.  *)
(*   destruct (analyze f (vanalyze rm f)) as [approx|] eqn:?; inv EQ.  *)
(*   exploit Mem.alloc_extends; eauto. apply Zle_refl. apply Zle_refl.  *)
(*   intros (m'' & A & B). *)
(*   econstructor; split. *)
(*   eapply exec_function_internal; simpl; eauto.  *)
(*   simpl. econstructor; eauto. *)
(*   eapply analysis_correct_entry; eauto. *)
(*   apply init_regs_lessdef; auto. *)

(* - (* external function *) *)
(*   monadInv H6.  *)
(*   exploit external_call_mem_extends; eauto. *)
(*   intros (v' & m1' & P & Q & R & S). *)
(*   econstructor; split. *)
(*   eapply exec_function_external; eauto. *)
(*   eapply external_call_symbols_preserved; eauto. *)
(*   exact symbols_preserved. exact varinfo_preserved. *)
(*   econstructor; eauto. *)

- (* return *)
  inv H2.
  econstructor; split.
  eapply exec_return; eauto.
  left. econstructor; eauto.
  apply set_reg_lessdef; auto.
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
    (MEASURE: i = WF.elt)
    (Hsrc: sound_state_ext fprog s1)
    (Htgt: sound_state_ext ftprog s2)
    (MS: match_states fprog s1 s2 \/ match_call fprog ftprog s1 s2)
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

Lemma match_states_state_lsim es es' eF F i s1 s1'
      (MS: match_states_ext fprog ftprog s1 s1'):
  @state_lsim Language_ext_RTL Language_ext_RTL transf_sigT _
              mrelT_ops fprog ftprog es es' eF F i s1 s1'.
Proof.
  revert F i s1 s1' MS. pcofix CIH. intros F i s1 s1' MS. pfold.
  inv MS. destruct (classic (exists r, final_state s1 r)).
  { destruct H as [rval Hrval]. eapply _state_lsim_term; eauto.
    - apply final_state_equiv. eauto.
    - apply final_state_equiv. eapply transf_final_states; eauto.
  }
  constructor; auto.
  { repeat intro. apply H. exists r0. apply final_state_equiv. auto. }
  intros. exploit transf_step_correct; eauto. simpl.
  intros [s2' [Hs2' Hmatch2]].
  exists WF.elt. exists s2'. exists tt.
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
    + intros. subst. inversion Hst2_mem. subst. destruct MS as [MS|MS]; [|inv MS].
      right. apply CIH. constructor; auto.
Qed.

Lemma transf_function'_lsim
      f approx
      (ANALYZE: analyze f (vanalyze (romem_for_program prog) f) = Some approx):
  @function_lsim Language_ext_RTL Language_ext_RTL transf_sigT _
                 mrelT_ops fprog ftprog f (transf_function' f approx).
Proof.
  constructor. intros. pfold. constructor; subst; auto.
  { intros ? Hfinal. apply final_state_equiv in Hfinal. inv Hfinal. }
  intros. destruct fd_src; inv Hfd_src. destruct fd_tgt; inv Hfd_tgt. inversion Hst2_src. subst.
  inv Hmrel_entry. destruct MS as [MS|MS]; inversion MS; subst.

  (* internal function *)
  exploit Mem.alloc_extends; eauto. apply Zle_refl. apply Zle_refl.
  intros (m'' & A & B).
  eexists. eexists. exists tt. split.
  left. apply plus_one. constructor; eauto.
  simpl. split; [auto|].
  cut (match_states fprog
                    (State es_src f (Vptr stk Int.zero) (fn_entrypoint f)
                           (init_regs args_src (fn_params f)) m')
                    (State es_tgt (transf_function' f approx) 
                           (Vptr stk Int.zero) (fn_entrypoint f)
                           (init_regs args_tgt (fn_params f)) m'')).
  { intro MS2. split; [constructor; eauto|].
    { eapply sound_past_step; eauto. }
    { eapply sound_past_step; eauto.
      apply (exec_function_internal _ es_tgt (transf_function' f approx)). auto.
    }
    constructor. left. apply match_states_state_lsim. constructor; auto.
    - eapply sound_past_step; eauto.
    - eapply sound_past_step; eauto.
      apply (exec_function_internal _ es_tgt (transf_function' f approx)). auto.
  }
  simpl. econstructor; eauto.
  apply program_linkeq_romem_le. auto.
  eapply analysis_correct_entry; eauto.
  apply init_regs_lessdef; auto.
Qed.

End STATE_LSIM.

Lemma CSE_program_lsim:
  @program_lsim Language_RTL Language_RTL transf_sigT transf_efT transf_vT
                (@function_lsim Language_ext_RTL Language_ext_RTL transf_sigT _ mrelT_ops)
                prog tprog.
Proof.
  generalize transf_function'_lsim.
  destruct prog as [defs main]. simpl in *.
  unfold transf_program, transform_partial_program, transform_partial_program2 in TRANSF.
  monadInv TRANSF. rename x into tdefs.
  simpl in *. intro Hlsim. constructor; simpl; auto.
  revert Hlsim EQ.
  generalize tdefs at 2 as ftdefs.
  generalize defs at 1 2 3 5 as fdefs.
  revert defs tdefs.
  induction defs; simpl; intros tdefs fdefs ftdefs Hlsim Hglobdefs; inv Hglobdefs; try constructor.
  destruct a. destruct g.
  - match goal with
      | [H: match ?tf with | OK _ => _ | Error _ => _ end = _ |- _] => destruct tf eqn:Htf; inv H
    end.
    monadInv H1. constructor; simpl in *; try apply IHdefs; auto.
    split; auto. apply (@globdef_lsim_fun Language_RTL Language_RTL).
    destruct f; simpl in *.
    + monadInv Htf. constructor; simpl; intros.
      unfold transf_function in EQ0.
      match goal with
        | [H: match ?a with | Some _ => _ | None => _ end = _ |- _] => destruct a as [a'|] eqn:Hanalyze; inv H
      end.
      simpl. split; auto. repeat intro.
      apply Hlsim; auto.
    + inv Htf.
      eapply globfun_lsim_intro; eauto; simpl; auto.
  - monadInv H0. constructor; simpl in *; try apply IHdefs; auto.
    split; auto. apply (@globdef_lsim_var Language_RTL Language_RTL).
    repeat constructor.
Qed.

End PRESERVATION.
