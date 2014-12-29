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
Require Import CSE.
Require Import CSEproof.
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
Hypothesis TRANSF: transf_program prog = OK tprog.

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
Proof.
  apply program_linkeq_romem_le. auto.
Qed.

Inductive match_stackframes (es es':list stackframe): list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes es es' es es'
  | match_stackframes_cons:
      forall res sp pc rs f approx s rs' s'
           (ANALYZE: analyze f (vanalyze rm f) = Some approx)
           (SAT: forall v m, exists valu, numbering_holds valu ge sp (rs#res <- v) m approx!!pc)
           (RLD: regs_lessdef rs rs')
           (STACKS: match_stackframes es es' s s'),
    match_stackframes es es'
      (Stackframe res f sp pc rs :: s)
      (Stackframe res (transf_function' f approx) sp pc rs' :: s').

Inductive match_states (es es':list stackframe): state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m s' rs' m' f approx
             (ANALYZE: analyze f (vanalyze rm f) = Some approx)
             (SAT: exists valu, numbering_holds valu ge sp rs m approx!!pc)
             (RLD: regs_lessdef rs rs')
             (MEXT: Mem.extends m m')
             (STACKS: match_stackframes es es' s s'),
      match_states es es'
                   (State s f sp pc rs m)
                   (State s' (transf_function' f approx) sp pc rs' m')
  | match_states_return:
      forall s s' v v' m m',
      match_stackframes es es' s s' ->
      Val.lessdef v v' ->
      Mem.extends m m' ->
      match_states es es'
                   (Returnstate s v m)
                   (Returnstate s' v' m').

Inductive match_call (es es':list stackframe): state -> state -> Prop :=
  | match_states_call:
      forall s f tf args m s' args' m',
      match_stackframes es es' s s' ->
      fundef_weak_lsim
        (common_fundef_dec (F:=function)) fn_sig
        (common_fundef_dec (F:=function)) fn_sig
        ge tge f tf ->
      Val.lessdef_list args args' ->
      Mem.extends m m' ->
      match_call es es'
                 (Callstate s f args m)
                 (Callstate s' tf args' m').

Inductive match_return (es es':list stackframe): state -> state -> Prop :=
  | match_return_intro:
      forall v v' m m',
      match_stackframes es es' es es' ->
      Val.lessdef v v' ->
      Mem.extends m m' ->
      match_return es es'
                   (Returnstate es v m)
                   (Returnstate es' v' m').

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc ?c = Some ?instr), f: function, approx: PMap.t numbering |- _ =>
      cut ((transf_function' f approx).(fn_code)!pc = Some(transf_instr approx!!pc instr));
      [ simpl transf_instr
      | unfold transf_function', transf_code; simpl; rewrite PTree.gmap; 
        unfold option_map; rewrite H1; reflexivity ]
  end.

Lemma transf_step_correct:
  forall es es' s1 t s2, step ge s1 t s2 ->
  forall s1' (MS: match_states es es' s1 s1') (NMR: ~ match_return es es' s1 s1') (SOUND: sound_state_ext fprog s1),
  exists s2', step tge s1' t s2' /\ (match_states es es' s2 s2' \/ match_call es es' s2 s2').
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
  inv SOUND. specialize (Hsound _ rm_frm). inv Hsound.
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
    inv SOUND. specialize (Hsound _ rm_frm). inv Hsound. eapply add_memcpy_holds; eauto. 
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
  { contradict NMR. constructor; auto. constructor; auto. }
  econstructor; split.
  eapply exec_return; eauto.
  left. econstructor; eauto.
  apply set_reg_lessdef; auto.
Qed.

Inductive match_states_ext es es' st tst: Prop :=
| match_states_ext_intro
    (Hmatch: match_states es es' st tst)
    (Hsrc: sound_state_ext fprog st)
    (Htgt: sound_state_ext ftprog tst)
.

Lemma match_states_state_lsim es es' i:
  match_states_ext es es' <2= state_lsim mrelT_ops_extends fprog ftprog es es' tt tt i.
Proof.
  revert i. pcofix CIH. intros i s1 s1' MS. pfold.
  inv MS. destruct (classic (match_return es es' s1 s1')).
  { inv H. eapply _state_lsim_return; eauto.
    reflexivity.
  }
  constructor; auto.
  { intros ? Hfinal. inv Hfinal. inv Hmatch. inv H3.
    apply H. constructor; auto. constructor.
  }
  intros. exploit transf_step_correct; eauto.
  intros [s2' [Hs2' Hmatch']].
  exists WF.elt. exists s2'. exists tt. simpl.
  split; [left; apply plus_one; auto|].
  split; [auto|].
  split; [destruct Hmatch' as [Hmatch'|Hmatch']; inv Hmatch'; auto|].
  destruct Hmatch' as [Hmatch'|Hmatch'].
  - constructor. right. apply CIH. constructor; auto.
    + eapply sound_past_step; eauto.
    + eapply sound_past_step; eauto.
  - inv Hmatch'. eapply _state_lsim_or_csim_csim; eauto.
    { apply mrelT_ops_extends_lessdef_list. auto. }
    intros. right. destruct mrel2. apply CIH. constructor; auto.
    subst. constructor; auto.
Qed.

Lemma transf_function'_lsim
      f approx
      (ANALYZE: analyze f (vanalyze (romem_for_program prog) f) = Some approx):
  function_lsim mrelT_ops_extends fprog ftprog f (transf_function' f approx).
Proof.
  constructor. repeat intro. pfold. constructor; subst; auto.
  { intros ? Hfinal. inv Hfinal. }
  intros. inversion Hst2_src. subst.
  exists WF.elt. eexists. exists tt.
  split; [left; apply plus_one; eauto|].
  { econstructor; eauto.
    match goal with
      | [|- ?b = _] =>
        instantiate (1 := snd b); instantiate (1 := fst b); auto
    end.
  }
  split; [reflexivity|].
  simpl in *. exploit Mem.alloc_extends; eauto. apply Zle_refl. apply Zle_refl.
  intros (m'' & A & B).
  simpl. rewrite A. simpl. split; auto.
  apply _state_lsim_or_csim_lsim. left.
  destruct mrel_entry. apply match_states_state_lsim. split.
  - constructor; auto.
    + eapply analysis_correct_entry; eauto.
    + apply init_regs_lessdef; auto.
      eapply mrelT_ops_extends_lessdef_list.
      instantiate (1 := tt). eauto.
    + constructor.
  - eapply sound_past_step; eauto.
  - eapply sound_past_step; eauto.
    apply (exec_function_internal tge cs_entry_tgt (transf_function' f approx)).
    auto.
Qed.

End FUTURE.

Lemma CSE_program_lsim:
  program_lsim
    (@common_fundef_dec function) fn_sig
    (@common_fundef_dec function) fn_sig
    (@Errors.OK _)
    (function_lsim mrelT_ops_extends)
    prog tprog.
Proof.
  generalize transf_function'_lsim.
  destruct prog as [defs main]. clear prog. simpl in *.
  unfold transf_program, transform_partial_program in TRANSF.
  unfold transform_partial_program2 in TRANSF.
  match goal with
    | [H: bind ?b _ = OK _ |- _] =>
      destruct b as [tdefs|] eqn:Hglobdefs; inv H
  end.
  simpl in *. intro Hlsim. constructor; simpl; auto.
  revert Hlsim Hglobdefs.
  generalize tdefs at 2 as ftdefs.
  generalize defs at 1 2 3 5 as fdefs.
  revert defs tdefs.
  induction defs; simpl; intros tdefs fdefs ftdefs Hlsim Hglobdefs; inv Hglobdefs.
  { constructor. }
  { destruct a. destruct g.
    { match goal with
        | [H: match ?tf with | OK _ => _ | Error _ => _ end = _ |- _] =>
          destruct tf eqn:Htf; inv H
      end.
      match goal with
        | [H: bind ?b _ = OK _ |- _] =>
          destruct b eqn:Hglobdefs; inv H
      end.
      constructor; simpl in *.
      { split; auto. constructor.
        destruct f; simpl in *.
        { match goal with
            | [H: bind ?b _ = OK _ |- _] =>
              destruct b eqn:Htf'; inv H
          end.
          eapply globfun_lsim_i; eauto;
          unfold common_fundef_dec; eauto.
          unfold transf_function in Htf'.
          match goal with
            | [H: match ?a with | Some _ => _ | None => _ end = _ |- _] =>
              destruct a as [a'|] eqn:Hanalyze; inv H
          end.
          simpl. split; auto. repeat intro.
          apply Hlsim; auto.
        }
        { inv Htf.
          eapply globfun_lsim_e; eauto;
          unfold common_fundef_dec; eauto.
        }
      }
      { apply IHdefs; auto. }
    }
    { match goal with
        | [H: bind ?b _ = OK _ |- _] =>
          destruct b eqn:Hglobdefs; inv H
      end.
      constructor; simpl in *.
      { split; auto. repeat constructor. }
      apply IHdefs; auto.
    }
  }
Qed.

End PRESERVATION.
