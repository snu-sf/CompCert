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
Require Import NeedDomain.
Require Import NeedOp.
Require Import Deadcode.
Require Import Deadcodeproof.
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
  @globfun_lsim Language_RTL Language_RTL id (@Errors.OK _)
                (fun _ _ _ _ => True)
                fprog ftprog.

Let ge := Genv.globalenv fprog.
Let tge := Genv.globalenv ftprog.

Lemma stacksize_translated:
  forall f tf rm,
  transf_function rm f = OK tf -> tf.(fn_stacksize) = f.(fn_stacksize).
Proof.
  unfold transf_function; intros. destruct (analyze (vanalyze rm f) f); inv H; auto.
Qed.

Lemma transf_function_at:
  forall f tf an pc instr rm,
  transf_function rm f = OK tf ->
  analyze (vanalyze rm f) f = Some an ->
  f.(fn_code)!pc = Some instr ->
  tf.(fn_code)!pc = Some(transf_instr (vanalyze rm f) an pc instr).
Proof.
  intros. unfold transf_function in H. rewrite H0 in H. inv H; simpl. 
  rewrite PTree.gmap. rewrite H1; auto. 
Qed.

Hint Resolve is_dead_sound_1 is_dead_sound_2: na.

Lemma find_function_translated:
  forall ros rs fd trs ne,
  find_function ge ros rs = Some fd ->
  eagree rs trs (add_ros_need_all ros ne) ->
  exists tfd, find_function tge ros trs = Some tfd /\
              fundef_weak_lsim Language_RTL Language_RTL id ge tge fd tfd.
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
      forall res f sp pc e tf te an rm
        (RM: PTree_le rm (romem_for_program fprog))
        (FUN: transf_function rm f = OK tf)
        (ANL: analyze (vanalyze rm f) f = Some an)
        (RES: forall v tv,
              Val.lessdef v tv ->
              eagree (e#res <- v) (te#res<- tv)
                     (fst (transfer f (vanalyze rm f) pc an!!pc))),
      match_stackframes (Stackframe res f (Vptr sp Int.zero) pc e)
                        (Stackframe res tf (Vptr sp Int.zero) pc te).

Inductive match_states: state -> state -> Prop :=
  | match_regular_states:
      forall s f sp pc e m ts tf te tm an rm
        (STACKS: list_forall2 match_stackframes s ts)
        (RM: PTree_le rm (romem_for_program fprog))
        (FUN: transf_function rm f = OK tf)
        (ANL: analyze (vanalyze rm f) f = Some an)
        (ENV: eagree e te (fst (transfer f (vanalyze rm f) pc an!!pc)))
        (MEM: magree m tm (nlive ge sp (snd (transfer f (vanalyze rm f) pc an!!pc)))),
      match_states (State s f (Vptr sp Int.zero) pc e m)
                   (State ts tf (Vptr sp Int.zero) pc te tm)
  | match_return_states:
      forall s v m ts tv tm
        (STACKS: list_forall2 match_stackframes s ts)
        (RES: Val.lessdef v tv)
        (MEM: Mem.extends m tm),
      match_states (Returnstate s v m)
                   (Returnstate ts tv tm).

Inductive match_call: state -> state -> Prop :=
  | match_call_states:
      forall s f args m ts tf targs tm
        (STACKS: list_forall2 match_stackframes s ts)
        (FUN: fundef_weak_lsim Language_RTL Language_RTL id ge tge f tf)
        (ARGS: Val.lessdef_list args targs)
        (MEM: Mem.extends m tm),
      match_call (Callstate s f args m)
                 (Callstate ts tf targs tm).

Lemma analyze_successors:
  forall f an pc instr pc' rm,
  analyze (vanalyze rm f) f = Some an ->
  f.(fn_code)!pc = Some instr ->
  In pc' (successors_instr instr) ->
  NA.ge an!!pc (transfer f (vanalyze rm f) pc' an!!pc').
Proof.
  intros. eapply DS.fixpoint_solution; eauto.
  intros. unfold transfer; rewrite H2. destruct a. apply DS.L.eq_refl.
Qed.

Lemma match_succ_states:
  forall s f sp pc e m ts tf te tm an pc' instr ne nm rm
    (STACKS: list_forall2 match_stackframes s ts)
    (RM: PTree_le rm (romem_for_program fprog))
    (FUN: transf_function rm f = OK tf)
    (ANL: analyze (vanalyze rm f) f = Some an)
    (INSTR: f.(fn_code)!pc = Some instr)
    (SUCC: In pc' (successors_instr instr))
    (ANPC: an!!pc = (ne, nm))
    (ENV: eagree e te ne)
    (MEM: magree m tm (nlive ge sp nm)),
  match_states (State s f (Vptr sp Int.zero) pc' e m)
               (State ts tf (Vptr sp Int.zero) pc' te tm).
Proof.
  intros. exploit analyze_successors; eauto. rewrite ANPC; simpl. intros [A B]. 
  econstructor; eauto. 
  eapply eagree_ge; eauto. 
  eapply magree_monotone; eauto. intros; apply B; auto.  
Qed.

Theorem step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1', match_states S1 S1' -> sound_state_ext fprog S1 ->
  exists S2', step tge S1' t S2' /\ (match_states S2 S2' \/ match_call S2 S2').
Proof.

Ltac TransfInstr :=
  match goal with
  | [INSTR: (fn_code _)!_ = Some _,
     FUN: transf_function _ _ = OK _,
     ANL: analyze _ _ = Some _ |- _ ] =>
       generalize (transf_function_at _ _ FUN ANL INSTR);
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

  induction 1; intros S1' MS SS; inv MS.

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
    inv SS. specialize (Hsound _ RM). inv Hsound. intros. eapply nlive_add; eauto. constructor. apply GE. auto. 
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
  inv STACKS. inv H1. 
  econstructor; split.
  constructor. 
  left. econstructor; eauto. apply mextends_agree; auto. 
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
  intros. inv H0. inv H. inv STACKS. inv RES. constructor. 
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
  exploit transf_initial_states; eauto. intros [s2' [Hs2' Hinit]].
  generalize (initial_state_unique Hs2' H2). intro. subst.
  exists tt. eexists. constructor; auto.
  - apply sound_initial. auto.
  - apply sound_initial. auto.
Qed.
Next Obligation.
  apply (mrelT_ops_lessdef_list mrel args1 args2) in Hargs.
  inv Hs0. inv Hmrel. destruct MS as [MS|MS]; inv MS.
  inv Hfd1. destruct fd2; inv Hfd2.

  (* external function *)
  exploit external_call_mem_extends; eauto.
  intros [v' [m2' [A [B [C D]]]]].
  exists tt. eexists. eexists. eexists. eexists. split; eauto.
  cut (step (Genv.globalenv p2) (Callstate cs2 (External ef2) args2 m2) evt (Returnstate cs2 v' m2')).
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
    eapply transf_final_states; eauto.
  }
  constructor; auto.
  { repeat intro. apply H. exists r0. auto. }
  intros. exploit step_simulation; eauto. simpl.
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

Lemma transf_function_lsim
      f tf (Hf: transf_function (romem_for_program prog) f = OK tf):
  @function_lsim Language_ext_RTL Language_ext_RTL transf_sigT _
                 mrelT_ops fprog ftprog f tf.
Proof.
  constructor. intros. pfold. constructor; subst; auto.
  { intros ? Hfinal. inv Hfinal. }
  intros. destruct fd_src; inv Hfd_src. destruct fd_tgt; inv Hfd_tgt. inversion Hst2_src. subst.
  inv Hmrel_entry. destruct MS as [MS|MS]; inversion MS; subst.

  (* internal function *)
  generalize Hf. unfold transf_function. intros EQ'.
  destruct (analyze (vanalyze (romem_for_program prog) f) f) as [an|] eqn:AN; inv EQ'.
  exploit Mem.alloc_extends; eauto. apply Zle_refl. apply Zle_refl.
  intros (tm' & A & B).
  exists WF.elt. eexists. exists tt. split.
  left. apply plus_one. econstructor; simpl; eauto.
  simpl. split; [auto|].
  cut (match_states fprog
         (State es_src f (Vptr stk Int.zero) (fn_entrypoint f)
                (init_regs args_src (fn_params f)) m')
         (State es_tgt
                {|
                  fn_sig := fn_sig f;
                  fn_params := fn_params f;
                  fn_stacksize := fn_stacksize f;
                  fn_code := PTree.map
                               (transf_instr (vanalyze (romem_for_program prog) f) an)
                               (fn_code f);
                  fn_entrypoint := fn_entrypoint f |} (Vptr stk Int.zero)
                (fn_entrypoint f) (init_regs args_tgt (fn_params f)) tm')).
  { intro MS2. split; [constructor; eauto|].
    { eapply sound_past_step; eauto. }
    { eapply sound_past_step; eauto.
      eapply (exec_function_internal _ es_tgt (mkfunction _ _ _ _ _)). eauto.
    }
    constructor. left. apply match_states_state_lsim. constructor; auto.
    - eapply sound_past_step; eauto.
    - eapply sound_past_step; eauto.
      eapply (exec_function_internal _ es_tgt (mkfunction _ _ _ _ _)). eauto.
  }
  simpl. econstructor; eauto.
  apply program_linkeq_romem_le. auto.
  apply eagree_init_regs; auto.
  apply mextends_agree; auto.
Qed.

End STATE_LSIM.

Lemma Deadcode_program_lsim:
  @program_lsim Language_RTL Language_RTL transf_sigT transf_efT transf_vT
                (@function_lsim Language_ext_RTL Language_ext_RTL transf_sigT _ mrelT_ops)
                prog tprog.
Proof.
  generalize transf_function_lsim.
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
      unfold transf_function. rewrite Hanalyze. auto.
    + inv Htf.
      eapply globfun_lsim_intro; eauto; simpl; auto.
  - monadInv H0. constructor; simpl in *; try apply IHdefs; auto.
    split; auto. apply (@globdef_lsim_var Language_RTL Language_RTL).
    repeat constructor.
Qed.

End PRESERVATION.
