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
Require Import NeedDomain.
Require Import NeedOp.
Require Import Deadcode.
Require Import Deadcodeproof.
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
Proof. apply program_linkeq_romem_le. auto. Qed.
Hint Resolve rm_frm.

Hint Resolve is_dead_sound_1 is_dead_sound_2: na.

Lemma find_function_translated:
  forall ros rs fd trs ne,
  find_function ge ros rs = Some fd ->
  eagree rs trs (add_ros_need_all ros ne) ->
  exists tfd, find_function tge ros trs = Some tfd /\
              fundef_weak_lsim
                (@common_fundef_dec function) fn_sig
                (@common_fundef_dec function) fn_sig
                ge tge fd tfd.
Proof.
  intros. destruct ros as [r|id]; simpl in *.
- assert (LD: Val.lessdef rs#r trs#r) by eauto with na. inv LD.
  apply functions_translated; auto.
  rewrite <- H2 in H; discriminate.
- unfold tge. erewrite symbols_preserved; eauto. fold ge. destruct (Genv.find_symbol ge id); try discriminate.
  apply funct_ptr_translated; auto.
Qed.

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  | match_stackframes_intro:
      forall res f sp pc e tf te an
        (FUN: transf_function rm f = OK tf)
        (ANL: analyze (vanalyze rm f) f = Some an)
        (RES: forall v tv,
              Val.lessdef v tv ->
              eagree (e#res <- v) (te#res<- tv)
                     (fst (transfer f (vanalyze rm f) pc an!!pc))),
      match_stackframes (Stackframe res f (Vptr sp Int.zero) pc e)
                        (Stackframe res tf (Vptr sp Int.zero) pc te).

Inductive match_stackframes_ext (es es':list stackframe): list stackframe -> list stackframe -> Prop :=
  | match_stackframes_ext_nil:
      match_stackframes_ext es es' es es'
  | match_stackframes_ext_cons s s' fr fr'
      (HS: match_stackframes_ext es es' s s')
      (HFR: match_stackframes fr fr'):
      match_stackframes_ext es es' (fr::s) (fr'::s')
.

Inductive match_states (es es':list stackframe): state -> state -> Prop :=
  | match_regular_states:
      forall s f sp pc e m ts tf te tm an
        (STACKS: match_stackframes_ext es es' s ts)
        (FUN: transf_function rm f = OK tf)
        (ANL: analyze (vanalyze rm f) f = Some an)
        (ENV: eagree e te (fst (transfer f (vanalyze rm f) pc an!!pc)))
        (MEM: magree m tm (nlive ge sp (snd (transfer f (vanalyze rm f) pc an!!pc)))),
      match_states es es'
                   (State s f (Vptr sp Int.zero) pc e m)
                   (State ts tf (Vptr sp Int.zero) pc te tm)
  | match_return_states:
      forall s v m ts tv tm
        (STACKS: match_stackframes_ext es es' s ts)
        (RES: Val.lessdef v tv)
        (MEM: Mem.extends m tm),
      match_states es es'
                   (Returnstate s v m)
                   (Returnstate ts tv tm).

Inductive match_call (es es':list stackframe): state -> state -> Prop :=
  | match_call_states:
      forall s f args m ts tf targs tm
        (STACKS: match_stackframes_ext es es' s ts)
        (FUN: fundef_weak_lsim
                (@common_fundef_dec function) fn_sig
                (@common_fundef_dec function) fn_sig
                ge tge f tf)
        (ARGS: Val.lessdef_list args targs)
        (MEM: Mem.extends m tm),
      match_call es es'
                 (Callstate s f args m)
                 (Callstate ts tf targs tm).

Inductive match_return (es es':list stackframe): state -> state -> Prop :=
  | match_return_return:
      forall s v m ts tv tm
        (STACKS: match_stackframes_ext es es' s ts)
        (RES: Val.lessdef v tv)
        (MEM: Mem.extends m tm),
      match_return es es'
                   (Returnstate s v m)
                   (Returnstate ts tv tm).

Lemma match_succ_states:
  forall es es' s f sp pc e m ts tf te tm an pc' instr ne nm
    (STACKS: match_stackframes_ext es es' s ts)
    (FUN: transf_function rm f = OK tf)
    (ANL: analyze (vanalyze rm f) f = Some an)
    (INSTR: f.(fn_code)!pc = Some instr)
    (SUCC: In pc' (successors_instr instr))
    (ANPC: an!!pc = (ne, nm))
    (ENV: eagree e te ne)
    (MEM: magree m tm (nlive ge sp nm)),
  match_states es es'
               (State s f (Vptr sp Int.zero) pc' e m)
               (State ts tf (Vptr sp Int.zero) pc' te tm).
Proof.
  intros. exploit analyze_successors; eauto. rewrite ANPC; simpl. intros [A B]. 
  econstructor; eauto. 
  eapply eagree_ge; eauto. 
  eapply magree_monotone; eauto. intros; apply B; auto.  
Qed.

Theorem step_simulation:
  forall es es'  S1 t S2, step ge S1 t S2 ->
  forall S1', match_states es es' S1 S1' -> ~ match_return es es' S1 S1' -> sound_state_ext fprog S1 ->
  exists S2', step tge S1' t S2' /\ (match_states es es' S2 S2' \/ match_call es es' S2 S2').
Proof.

Ltac TransfInstr :=
  match goal with
  | [INSTR: (fn_code _)!_ = Some _,
     FUN: transf_function _ _ = OK _,
     ANL: analyze _ _ = Some _ |- _ ] =>
       generalize (transf_function_at _ _ _ _ _ _ FUN ANL INSTR);
       intro TI;
       unfold transf_instr in TI
  end.

Ltac UseTransfer :=
  match goal with
  | [INSTR: (fn_code _)!?pc = Some _,
     ANL: analyze _ _ = Some ?an |- _ ] =>
       destruct (an!!pc) as [ne nm] eqn:ANPC;
       unfold transfer in *;
       rewrite INSTR in *;
       simpl in *
  end.

  induction 1; intros S1' MS NMR SS; inv MS.

- (* nop *)
  TransfInstr; UseTransfer.
  econstructor; split.
  eapply exec_Inop; eauto. 
  left. eapply match_succ_states; eauto. simpl; auto.

- (* op *)
  TransfInstr; UseTransfer.
  destruct (is_dead (nreg ne res)) eqn:DEAD;
  [idtac|destruct (is_int_zero (nreg ne res)) eqn:INTZERO;
  [idtac|destruct (operation_is_redundant op (nreg ne res)) eqn:REDUNDANT]].
+ (* dead instruction, turned into a nop *)
  econstructor; split.
  eapply exec_Inop; eauto. 
  left. eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update_dead; auto with na. 
+ (* instruction with needs = [I Int.zero], turned into a load immediate of zero. *)
  econstructor; split.
  eapply exec_Iop with (v := Vint Int.zero); eauto. 
  left. eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; auto. 
  rewrite is_int_zero_sound by auto.
  destruct v; simpl; auto. apply iagree_zero.
+ (* redundant operation *)
  destruct args.
  * (* kept as is because no arguments -- should never happen *)
  simpl in *. 
  exploit needs_of_operation_sound. eapply ma_perm; eauto. 
  eauto. instantiate (1 := nreg ne res). eauto with na. eauto with na. intros [tv [A B]].
  econstructor; split. 
  eapply exec_Iop with (v := tv); eauto.
  rewrite <- A. apply eval_operation_preserved. apply symbols_preserved. auto.
  left. eapply match_succ_states; eauto. simpl; auto. 
  apply eagree_update; auto.
  * (* turned into a move *)
  unfold fst in ENV. unfold snd in MEM. simpl in H0.
  assert (VA: vagree v te#r (nreg ne res)).
  { eapply operation_is_redundant_sound with (arg1' := te#r) (args' := te##args).
    eauto. eauto. exploit add_needs_vagree; eauto. }
  econstructor; split.
  eapply exec_Iop; eauto. simpl; reflexivity. 
  left. eapply match_succ_states; eauto. simpl; auto. 
  eapply eagree_update; eauto 2 with na. 
+ (* preserved operation *)
  simpl in *.
  exploit needs_of_operation_sound. eapply ma_perm; eauto. eauto. eauto 2 with na. eauto with na.
  intros [tv [A B]].
  econstructor; split. 
  eapply exec_Iop with (v := tv); eauto.
  rewrite <- A. apply eval_operation_preserved. apply symbols_preserved. auto.
  left. eapply match_succ_states; eauto. simpl; auto. 
  apply eagree_update; eauto 2 with na.

- (* load *)
  TransfInstr; UseTransfer.
  destruct (is_dead (nreg ne dst)) eqn:DEAD;
  [idtac|destruct (is_int_zero (nreg ne dst)) eqn:INTZERO];
  simpl in *.
+ (* dead instruction, turned into a nop *)
  econstructor; split.
  eapply exec_Inop; eauto. 
  left. eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update_dead; auto with na. 
+ (* instruction with needs = [I Int.zero], turned into a load immediate of zero. *)
  econstructor; split.
  eapply exec_Iop with (v := Vint Int.zero); eauto. 
  left. eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; auto. 
  rewrite is_int_zero_sound by auto.
  destruct v; simpl; auto. apply iagree_zero.
+ (* preserved *)
  exploit eval_addressing_lessdef. eapply add_needs_all_lessdef; eauto. eauto. 
  intros (ta & U & V). inv V; try discriminate.
  destruct ta; simpl in H1; try discriminate.
  exploit magree_load; eauto.
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. apply nlive_add with bc i; assumption. 
  intros (tv & P & Q).
  econstructor; split.
  eapply exec_Iload with (a := Vptr b i). eauto. 
  rewrite <- U. apply eval_addressing_preserved. apply symbols_preserved. auto.
  eauto. 
  left. eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 2 with na. 
  eapply magree_monotone; eauto. intros. apply incl_nmem_add; auto. 

- (* store *)
  TransfInstr; UseTransfer.
  fold rm in TI.
  destruct (nmem_contains nm (aaddressing (vanalyze rm f) # pc addr args)
             (size_chunk chunk)) eqn:CONTAINS.
+ (* preserved *)
  simpl in *. 
  exploit eval_addressing_lessdef. eapply add_needs_all_lessdef; eauto. eauto. 
  intros (ta & U & V). inv V; try discriminate.
  destruct ta; simpl in H1; try discriminate.
  exploit magree_store_parallel. eauto. eauto. instantiate (1 := te#src). eauto with na.
  instantiate (1 := nlive ge sp0 nm). 
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. apply nlive_remove with bc b i; assumption. 
  intros (tm' & P & Q).
  econstructor; split.
  eapply exec_Istore with (a := Vptr b i). eauto. 
  rewrite <- U. apply eval_addressing_preserved. apply symbols_preserved. auto.
  eauto.
  left. eapply match_succ_states; eauto. simpl; auto.
  eauto 3 with na. 
+ (* dead instruction, turned into a nop *)
  destruct a; simpl in H1; try discriminate.
  econstructor; split.
  eapply exec_Inop; eauto. 
  left. eapply match_succ_states; eauto. simpl; auto.
  eapply magree_store_left; eauto.
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. eapply nlive_contains; eauto. 

- (* call *)
  TransfInstr; UseTransfer.
  exploit find_function_translated; eauto 2 with na. intros (tfd & A & B).
  econstructor; split.
  eapply exec_Icall; eauto. eapply sig_preserved; eauto. 
  right. constructor. 
  constructor; auto. econstructor; eauto. 
  intros.
  edestruct analyze_successors; eauto. simpl; eauto. 
  eapply eagree_ge; eauto. rewrite ANPC. simpl. 
  apply eagree_update; eauto with na.
  auto. eauto 2 with na. eapply magree_extends; eauto. apply nlive_all. 

- (* tailcall *)
  TransfInstr; UseTransfer.
  exploit find_function_translated; eauto 2 with na. intros (tfd & A & B).
  exploit magree_free. eauto. eauto. instantiate (1 := nlive ge stk nmem_all). 
  intros; eapply nlive_dead_stack; eauto. 
  intros (tm' & C & D). 
  econstructor; split.
  eapply exec_Itailcall; eauto. eapply sig_preserved; eauto. 
  erewrite stacksize_translated by eauto. eexact C.
  right. constructor; eauto 2 with na. eapply magree_extends; eauto. apply nlive_all.

- (* builtin *)
  TransfInstr; UseTransfer. revert ENV MEM TI.
  fold rm.
  functional induction (transfer_builtin (vanalyze rm f)#pc ef args res ne nm);
  simpl in *; intros.
+ (* volatile load *)
  assert (LD: Val.lessdef rs#a1 te#a1) by eauto 2 with na.
  inv H0. rewrite <- H1 in LD; inv LD.
  assert (X: exists tv, volatile_load ge chunk tm b ofs t tv /\ Val.lessdef v tv).
  {
    inv H2. 
  * exists (Val.load_result chunk v0); split; auto. constructor; auto. 
  * exploit magree_load; eauto. 
    exploit aaddr_sound; eauto. intros (bc & A & B & C).
    intros. eapply nlive_add; eassumption. 
    intros (tv & P & Q). 
    exists tv; split; auto. constructor; auto. 
  }
  destruct X as (tv & A & B).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved.
  simpl. rewrite <- H4. constructor. eauto.   
  apply symbols_preserved. auto. apply varinfo_preserved. auto.
  left. eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 2 with na.
  eapply magree_monotone; eauto. intros. apply incl_nmem_add; auto. 
+ (* volatile global load *)
  inv H0. 
  assert (X: exists tv, volatile_load ge chunk tm b ofs t tv /\ Val.lessdef v tv).
  {
    inv H2. 
  * exists (Val.load_result chunk v0); split; auto. constructor; auto. 
  * exploit magree_load; eauto.
    inv SS. specialize (Hsound _ rm_frm). inv Hsound. intros. eapply nlive_add; eauto. constructor. apply GE. auto. 
    intros (tv & P & Q). 
    exists tv; split; auto. constructor; auto. 
  }
  destruct X as (tv & A & B).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved.
  simpl. econstructor; eauto.   
  apply symbols_preserved. auto. apply varinfo_preserved. auto.
  left. eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 2 with na.
  eapply magree_monotone; eauto. intros. apply incl_nmem_add; auto. 
+ (* volatile store *)
  exploit transf_volatile_store. eauto. 
  instantiate (1 := te#a1). eauto 3 with na.
  instantiate (1 := te#a2). eauto 3 with na. 
  eauto.
  intros (EQ & tm' & A & B). subst v. 
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved. simpl; eauto. 
  apply symbols_preserved. auto. apply varinfo_preserved. auto.
  left. eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 3 with na.
+ (* volatile global store *)
  rewrite volatile_store_global_charact in H0. destruct H0 as (b & P & Q).
  exploit transf_volatile_store. eauto. eauto. 
  instantiate (1 := te#a1). eauto 2 with na. 
  eauto.
  intros (EQ & tm' & A & B). subst v. 
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved. simpl. 
  rewrite volatile_store_global_charact. exists b; split; eauto. 
  apply symbols_preserved. auto. apply varinfo_preserved. auto.
  left. eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 2 with na.
+ (* memcpy *)
  rewrite e1 in TI.
  inv H0. 
  set (adst := aaddr (vanalyze rm f) # pc dst) in *.
  set (asrc := aaddr (vanalyze rm f) # pc src) in *.
  exploit magree_loadbytes. eauto. eauto. 
  exploit aaddr_sound. eauto. eauto. symmetry; eexact H2.
  intros (bc & A & B & C).
  intros. eapply nlive_add; eassumption. 
  intros (tbytes & P & Q).
  exploit magree_storebytes_parallel.
  eapply magree_monotone. eexact MEM. 
  instantiate (1 := nlive ge sp0 (nmem_remove nm adst sz)).
  intros. apply incl_nmem_add; auto.
  eauto. 
  instantiate (1 := nlive ge sp0 nm). 
  exploit aaddr_sound. eauto. eauto. symmetry; eexact H1.
  intros (bc & A & B & C).
  intros. eapply nlive_remove; eauto.
  erewrite Mem.loadbytes_length in H10 by eauto. 
  rewrite nat_of_Z_eq in H10 by omega. auto.
  eauto. 
  intros (tm' & A & B).
  assert (LD1: Val.lessdef rs#src te#src) by eauto 3 with na. rewrite <- H2 in LD1.
  assert (LD2: Val.lessdef rs#dst te#dst) by eauto 3 with na. rewrite <- H1 in LD2.
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved. simpl.
  inv LD1. inv LD2. econstructor; eauto.  
  apply symbols_preserved. eauto. apply varinfo_preserved. auto.
  left. eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 3 with na.
+ (* memcpy eliminated *)
  rewrite e1 in TI. inv H0.
  set (adst := aaddr (vanalyze rm f) # pc dst) in *.
  set (asrc := aaddr (vanalyze rm f) # pc src) in *.
  econstructor; split.
  eapply exec_Inop; eauto. 
  left. eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_undef; auto.
  eapply magree_storebytes_left; eauto.
  exploit aaddr_sound. eauto. eauto. symmetry; eexact H1.
  intros (bc & A & B & C).
  intros. eapply nlive_contains; eauto.
  erewrite Mem.loadbytes_length in H0 by eauto. 
  rewrite nat_of_Z_eq in H0 by omega. auto.
+ (* annot *)
  inv H0. 
  econstructor; split. 
  eapply exec_Ibuiltin; eauto. 
  eapply external_call_symbols_preserved. simpl; constructor. 
  eapply eventval_list_match_lessdef; eauto 2 with na.
  apply symbols_preserved. auto. apply varinfo_preserved. auto.
  left. eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 2 with na.
+ (* annot val *)  
  inv H0. destruct _x; inv H1. destruct _x; inv H4.
  econstructor; split. 
  eapply exec_Ibuiltin; eauto. 
  eapply external_call_symbols_preserved. simpl; constructor. 
  eapply eventval_match_lessdef; eauto 2 with na.
  apply symbols_preserved. auto. apply varinfo_preserved. auto.
  left. eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 3 with na.
+ (* all other builtins *)
  assert ((fn_code tf)!pc = Some(Ibuiltin _x _x0 res pc')).
  {
    destruct _x; auto. destruct _x0; auto. destruct _x0; auto. destruct _x0; auto. contradiction. 
  }
  clear y TI. 
  exploit external_call_mem_extends; eauto 2 with na. 
  eapply magree_extends; eauto. intros. apply nlive_all. 
  intros (v' & tm' & A & B & C & D & E). 
  econstructor; split.
  eapply exec_Ibuiltin; eauto. 
  eapply external_call_symbols_preserved. eauto.
  apply symbols_preserved. auto. apply varinfo_preserved. auto.
  left. eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 3 with na.
  eapply mextends_agree; eauto. 

- (* conditional *)
  TransfInstr; UseTransfer.
  econstructor; split.
  eapply exec_Icond; eauto. 
  eapply needs_of_condition_sound. eapply ma_perm; eauto. eauto. eauto with na. 
  left. eapply match_succ_states; eauto 2 with na. 
  simpl; destruct b; auto. 

- (* jumptable *)
  TransfInstr; UseTransfer.
  assert (LD: Val.lessdef rs#arg te#arg) by eauto 2 with na. 
  rewrite H0 in LD. inv LD. 
  econstructor; split.
  eapply exec_Ijumptable; eauto. 
  left. eapply match_succ_states; eauto 2 with na. 
  simpl. eapply list_nth_z_in; eauto. 

- (* return *)
  TransfInstr; UseTransfer.
  exploit magree_free. eauto. eauto. instantiate (1 := nlive ge stk nmem_all). 
  intros; eapply nlive_dead_stack; eauto. 
  intros (tm' & A & B). 
  econstructor; split.
  eapply exec_Ireturn; eauto. 
  erewrite stacksize_translated by eauto. eexact A. 
  left. constructor; auto.
  destruct or; simpl; eauto 2 with na.
  eapply magree_extends; eauto. apply nlive_all.

(* - (* internal function *) *)
(*   monadInv FUN. generalize EQ. unfold transf_function. intros EQ'. *)
(*   destruct (analyze (vanalyze rm f) f) as [an|] eqn:AN; inv EQ'. *)
(*   exploit Mem.alloc_extends; eauto. apply Zle_refl. apply Zle_refl. *)
(*   intros (tm' & A & B).  *)
(*   econstructor; split. *)
(*   econstructor; simpl; eauto.  *)
(*   simpl. econstructor; eauto.  *)
(*   apply eagree_init_regs; auto.  *)
(*   apply mextends_agree; auto.  *)

(* - (* external function *) *)
(*   exploit external_call_mem_extends; eauto. *)
(*   intros (res' & tm' & A & B & C & D & E).  *)
(*   simpl in FUN. inv FUN. *)
(*   econstructor; split. *)
(*   econstructor; eauto. *)
(*   eapply external_call_symbols_preserved; eauto.  *)
(*   exact symbols_preserved. exact varinfo_preserved. *)
(*   econstructor; eauto.  *)

- (* return *)
  inv STACKS; [contradict NMR; repeat (constructor; auto)|].
  inv HFR.
  econstructor; split.
  constructor. 
  left. econstructor; eauto. apply mextends_agree; auto. 
Qed.

(* TODO *)

End FUTURE.

(* TODO *)

End PRESERVATION.
