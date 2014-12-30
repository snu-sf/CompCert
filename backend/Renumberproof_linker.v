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

Inductive match_frames_ext (es es':list stackframe): list stackframe -> list stackframe -> Prop :=
  | match_stackframes_ext_nil:
      match_frames_ext es es' es es'
  | match_stackframes_ext_cons s s' fr fr'
      (HS: match_frames_ext es es' s s')
      (HFR: match_frames fr fr'):
      match_frames_ext es es' (fr::s) (fr'::s')
.

Inductive match_states (es es':list stackframe): RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk'
        (STACKS: match_frames_ext es es' stk stk')
        (REACH: reach f pc),
      match_states es es'
                   (State stk f sp pc rs m)
                   (State stk' (transf_function f) sp (renum_pc (pnum f) pc) rs m)
  | match_returnstates: forall stk v m stk'
        (STACKS: match_frames_ext es es' stk stk'),
      match_states es es'
                   (Returnstate stk v m)
                   (Returnstate stk' v m).

Inductive match_call (es es':list stackframe): RTL.state -> RTL.state -> Prop :=
  | match_callstates: forall stk f args m stk' f'
        (STACKS: match_frames_ext es es' stk stk')
        (FUN: fundef_weak_lsim
                (@common_fundef_dec function) fn_sig
                (@common_fundef_dec function) fn_sig
                ge tge f f'),
      match_call es es'
                 (Callstate stk f args m)
                 (Callstate stk' f' args m).

Inductive match_return (es es':list stackframe): RTL.state -> RTL.state -> Prop :=
  | match_return_intro: forall v m
        (STACKS: match_frames_ext es es' es es'),
      match_return es es'
                   (Returnstate es v m)
                   (Returnstate es' v m).

Lemma step_simulation:
  forall es es'  S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', match_states es es' S1 S1' -> ~ match_return es es' S1 S1' ->
  exists S2', RTL.step tge S1' t S2' /\ (match_states es es' S2 S2' \/ match_call es es' S2 S2').
Proof.
  induction 1; intros S1' MS NMR; inv MS; try TR_AT.
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
  inv STACKS; [contradict NMR; repeat (constructor; auto)|].
  inv HFR.
  econstructor; split. 
  eapply exec_return; eauto. 
  left. constructor; auto.
Qed.

(* TODO *)

End FUTURE.

(* TODO *)

End PRESERVATION.
