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
Require Import ValueAnalysis_linker.
Require Import LinkerSpecification.
Require Import Linkeq ProgramSim.
Require Import RTLSim MemoryRelation.
Require Import WFType paco.

Set Implicit Arguments.

Section PRESERVATION.

Let transf_EF (ef:external_function) := OK ef.
Let transf_V (v_src:unit) := OK v_src.
Let fundef_dec := (@common_fundef_dec function).

Variable fprog: program.
Variable ftprog: program.
Hypothesis (Hweak_sim:
              program_weak_sim
                fundef_dec fundef_dec transf_EF transf_V
                fprog ftprog).

Let globfun_weak_sim :=
  globfun_sim fundef_dec fundef_dec transf_EF (fun _ _ _ _ => True) fprog ftprog.

Let ge := Genv.globalenv fprog.
Let tge := Genv.globalenv ftprog.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: transf_program prog = OK tprog.
Hypothesis (Hfprog: program_linkeq (@common_fundef_dec function) prog fprog).
Hypothesis (Hftprog: program_linkeq (@common_fundef_dec function) tprog ftprog).
Let rm := romem_for_program prog.

Lemma rm_frm: romem_le rm (romem_for_program fprog).
Proof. admit. Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (find_symbol_match Hweak_sim).

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. exploit find_var_info_match; eauto. instantiate (1 := b).
  unfold ge, tge.
  destruct (Genv.find_var_info (Genv.globalenv ftprog) b), (Genv.find_var_info (Genv.globalenv fprog) b); intros; auto.
  - inv H. destruct g0; auto.
  - inv H.
  - inv H.
Qed.

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ fundef_sim ge tge f tf.
Proof.
  intros. exploit find_funct_ptr_match; eauto. intros [tf [Htf Hsim]].
  exists tf. split; auto. econstructor; eauto.
Qed.

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ fundef_sim ge tge f tf.
Proof.
  unfold Genv.find_funct. destruct v; intros sf Hsf; inv Hsf.
  destruct (Int.eq_dec i Int.zero); inv H0.
  apply funct_ptr_translated. auto.
Qed.

Lemma find_function_translated:
  forall ros rs fd rs',
  find_function ge ros rs = Some fd ->
  regs_lessdef rs rs' ->
  exists tfd, find_function tge ros rs' = Some tfd /\ fundef_sim ge tge fd tfd.
Proof.
  unfold find_function; intros; destruct ros.
- specialize (H0 r). inv H0.
  apply functions_translated; auto.
  rewrite <- H2 in H; discriminate.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

Inductive match_local (s s':list stackframe): state -> state -> Prop :=
  | match_states_intro:
      forall sp pc rs m rs' m' f approx
             (ANALYZE: analyze f (vanalyze rm f) = Some approx)
             (SAT: exists valu, numbering_holds valu ge sp rs m approx!!pc)
             (RLD: regs_lessdef rs rs')
             (MEXT: Mem.extends m m'),
      match_local s s'
                  (State s f sp pc rs m)
                  (State s' (transf_function' f approx) sp pc rs' m')
  | match_states_call:
      forall f tf args m args' m',
      forall pres psp ppc prs pf papprox prs'
             (PANALYZE: analyze pf (vanalyze rm pf) = Some papprox)
             (PSAT: forall v m, exists valu, numbering_holds valu ge psp (prs#pres <- v) m papprox!!ppc)
             (PRLD: regs_lessdef prs prs'),
      fundef_sim ge tge f tf ->
      Val.lessdef_list args args' ->
      Mem.extends m m' ->
      match_local s s'
                  (Callstate (Stackframe pres pf psp ppc prs :: s) f args m)
                  (Callstate (Stackframe pres (transf_function' pf papprox) psp ppc prs' :: s') tf args' m')
  | match_states_tailcall:
      forall f tf args m args' m',
      fundef_sim ge tge f tf ->
      Val.lessdef_list args args' ->
      Mem.extends m m' ->
      match_local s s'
                  (Callstate s f args m)
                  (Callstate s' tf args' m')
  | match_states_return:
      forall v v' m m',
      Val.lessdef v v' ->
      Mem.extends m m' ->
      match_local s s'
                  (Returnstate s v m)
                  (Returnstate s' v' m')
.

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc ?c = Some ?instr), f: function, approx: PMap.t numbering |- _ =>
      cut ((transf_function' f approx).(fn_code)!pc = Some(transf_instr approx!!pc instr));
      [ simpl transf_instr
      | unfold transf_function', transf_code; simpl; rewrite PTree.gmap; 
        unfold option_map; rewrite H1; reflexivity ]
  end.

Lemma transf_step_correct:
  forall s s' s1 t s2, step ge s1 t s2 ->
  forall (Hnormal: is_true (is_normal_state s1)),
  forall s1' (MS: match_local s s' s1 s1') (SOUND: sound_state_ext fprog s1),
  exists s2', step tge s1' t s2' /\ match_local s s' s2 s2'.
Proof.
  induction 1; intros; inv Hnormal; inv MS; try (TransfInstr; intro C).

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
  inv SOUND. specialize (Hsound _ rm_frm). inv Hsound.
  eapply add_store_result_hold; eauto.
  eapply kill_loads_after_store_holds; eauto.

- (* Icall *)
  exploit find_function_translated; eauto. intros [tf [FIND' TRANSF']].
  econstructor; split.
  eapply exec_Icall; eauto.
  admit. (* apply sig_preserved; auto. *)
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
  admit. (* apply sig_preserved; auto. *)
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
    inv SOUND. specialize (Hsound _ rm_frm). inv Hsound.
    eapply add_memcpy_holds; eauto. 
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
Qed.

Lemma match_local_state_lsim s s':
  match_local s s' <2= state_lsim mrelT_ops_extends ge tge s s' tt tt WF.elt.
Proof.
  pcofix CIH. intros s1 s1' MS. pfold.
  inversion MS; subst.
  - apply _state_lsim_step. intros. left. exists WF.elt.
    exploit transf_step_correct; eauto.
    { admit. (* sound_state *) }
    intros [s2' [Hs2' Hmatch']].
    eexists. exists tt.
    split; [apply plus_one; eauto|].
    split; [reflexivity|].
    split; [inv Hmatch'; auto|].
    right. auto.
  - eapply _state_lsim_call; eauto.
    + apply star_refl.
    + apply mrelT_ops_extends_lessdef_list. auto.
    + instantiate (1 := tt). reflexivity.
    + intros. exists WF.elt. destruct mrel3.
      right. apply CIH. subst. constructor; auto.
      apply set_reg_lessdef; auto.
  - eapply _state_lsim_tailcall; eauto.
    + apply star_refl.
    + apply mrelT_ops_extends_lessdef_list. auto.
    + instantiate (1 := tt). reflexivity.
    + reflexivity.
  - eapply _state_lsim_return; eauto.
    + apply star_refl.
    + instantiate (1 := tt). reflexivity.
    + reflexivity.
Qed.

End PRESERVATION.
