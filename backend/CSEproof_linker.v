Require Import Coqlib.
Require Import Maps.
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
Require Import CSE.
Require Import CSEproof.

Section PRESERVATION.

Variable prog: program.
Variable tprog : program.
Hypothesis TRANSF: transf_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Let rm := romem_for_program prog.

Inductive match_local: state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m s' rs' m' f approx
             (ANALYZE: analyze f (vanalyze rm f) = Some approx)
             (SAT: exists valu, numbering_holds valu ge sp rs m approx!!pc)
             (RLD: regs_lessdef rs rs')
             (MEXT: Mem.extends m m'),
      match_local (State s f sp pc rs m)
                  (State s' (transf_function' f approx) sp pc rs' m')
  | match_states_call:
      forall s f tf args m s' args' m',
      transf_fundef rm f = OK tf ->
      Val.lessdef_list args args' ->
      Mem.extends m m' ->
      match_local (Callstate s f args m)
                  (Callstate s' tf args' m')
  | match_states_return:
      forall s s' v v' m m',
      Val.lessdef v v' ->
      Mem.extends m m' ->
      match_local (Returnstate s v m)
                  (Returnstate s' v' m').

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc ?c = Some ?instr), f: function, approx: PMap.t numbering |- _ =>
      cut ((transf_function' f approx).(fn_code)!pc = Some(transf_instr approx!!pc instr));
      [ simpl transf_instr
      | unfold transf_function', transf_code; simpl; rewrite PTree.gmap; 
        unfold option_map; rewrite H1; reflexivity ]
  end.

(** The proof of simulation is a case analysis over the transition
  in the source code. *)

Lemma transf_step_correct:
  forall s1 t s2, step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1') (SOUND: sound_state prog s1),
  exists s2', step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS; try (TransfInstr; intro C).

  (* Inop *)
- econstructor; split.
  eapply exec_Inop; eauto.
  econstructor; eauto. 
  eapply analysis_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H; auto.

  (* Iop *)
- destruct (is_trivial_op op) eqn:TRIV.
+ (* unchanged *)
  exploit eval_operation_lessdef. eapply regs_lessdef_regs; eauto. eauto. eauto.
  intros [v' [A B]].
  econstructor; split.
  eapply exec_Iop with (v := v'); eauto.
  rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto. 
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
  econstructor; eauto. 
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
  rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto.
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
  econstructor; eauto. 
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
  { rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved. }
  exploit Mem.loadv_extends; eauto. 
  intros [v' [X Y]].
  econstructor; split.
  eapply exec_Iload; eauto.
  econstructor; eauto.
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
  { rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved. }
  exploit Mem.storev_extends; eauto. intros [m'' [X Y]].
  econstructor; split.
  eapply exec_Istore; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H.
  inv SOUND.
  eapply add_store_result_hold; eauto. 
  eapply kill_loads_after_store_holds; eauto.

- (* Icall *)
  exploit find_function_translated; eauto. intros [tf [FIND' TRANSF']]. 
  econstructor; split.
  eapply exec_Icall; eauto.
  apply sig_preserved; auto.
  econstructor; eauto. 
  econstructor; eauto. 
  intros. eapply analysis_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. 
  exists (fun _ => Vundef); apply empty_numbering_holds.
  apply regs_lessdef_regs; auto.

- (* Itailcall *)
  exploit find_function_translated; eauto. intros [tf [FIND' TRANSF']]. 
  exploit Mem.free_parallel_extends; eauto. intros [m'' [A B]].
  econstructor; split.
  eapply exec_Itailcall; eauto.
  apply sig_preserved; auto.
  econstructor; eauto. 
  apply regs_lessdef_regs; auto.

- (* Ibuiltin *)
  exploit external_call_mem_extends; eauto.
  instantiate (1 := rs'##args). apply regs_lessdef_regs; auto.
  intros (v' & m1' & P & Q & R & S).
  econstructor; split.
  eapply exec_Ibuiltin; eauto. 
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.
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
    inv SOUND. eapply add_memcpy_holds; eauto. 
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
  econstructor; eauto.
  destruct b; eapply analysis_correct_1; eauto; simpl; auto;
  unfold transfer; rewrite H; auto.

- (* Ijumptable *)
  generalize (RLD arg); rewrite H0; intro LD; inv LD.
  econstructor; split.
  eapply exec_Ijumptable; eauto. 
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl. eapply list_nth_z_in; eauto.
  unfold transfer; rewrite H; auto.

- (* Ireturn *)
  exploit Mem.free_parallel_extends; eauto. intros [m'' [A B]].
  econstructor; split.
  eapply exec_Ireturn; eauto.
  econstructor; eauto.
  destruct or; simpl; auto. 

- (* internal function *)
  monadInv H6. unfold transf_function in EQ. 
  destruct (analyze f (vanalyze rm f)) as [approx|] eqn:?; inv EQ. 
  exploit Mem.alloc_extends; eauto. apply Zle_refl. apply Zle_refl. 
  intros (m'' & A & B).
  econstructor; split.
  eapply exec_function_internal; simpl; eauto. 
  simpl. econstructor; eauto.
  eapply analysis_correct_entry; eauto.
  apply init_regs_lessdef; auto.

- (* external function *)
  monadInv H6. 
  exploit external_call_mem_extends; eauto.
  intros (v' & m1' & P & Q & R & S).
  econstructor; split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.

- (* return *)
  inv H2.
  econstructor; split.
  eapply exec_return; eauto.
  econstructor; eauto.
  apply set_reg_lessdef; auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. 
  exploit funct_ptr_translated; eauto. intros [tf [A B]].
  exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
  eapply Genv.init_mem_transf_partial; eauto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry. eapply transform_partial_program_main; eauto.
  rewrite <- H3. apply sig_preserved; auto.
  constructor. constructor. auto. auto. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H5. inv H3. constructor. 
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_step with
    (match_states := fun s1 s2 => sound_state prog s1 /\ match_states s1 s2).
- eexact symbols_preserved.
- intros. exploit transf_initial_states; eauto. intros [s2 [A B]]. 
  exists s2. split. auto. split. apply sound_initial; auto. auto.
- intros. destruct H. eapply transf_final_states; eauto.
- intros. destruct H0. exploit transf_step_correct; eauto. 
  intros [s2' [A B]]. exists s2'; split. auto. split. eapply sound_step; eauto. auto.
Qed.

End PRESERVATION.
