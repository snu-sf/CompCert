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
Require Import Tailcall.
Require Import Tailcallproof.
Require Import LinkerSpecification Linkeq.
Require Import ProgramLSim.
Require Import RTLLSim ValueAnalysis_linker.
Require Import WFType paco.

Section PRESERVATION.

Let transf_EF (ef:external_function) := OK ef.
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
Proof.
  apply program_linkeq_romem_le. auto.
Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (symbols_preserved Hfsim).

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. exploit varinfo_preserved.
  { instantiate (1 := ftprog). instantiate (1 := fprog). apply Hfsim. }
  instantiate (1 := b). unfold ge, tge.
  destruct (Genv.find_var_info (Genv.globalenv ftprog) b), (Genv.find_var_info (Genv.globalenv fprog) b); intros; auto; inv H.
  destruct g0; auto.
Qed.

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\
             fundef_weak_lsim
               (@common_fundef_dec function) fn_sig
               (@common_fundef_dec function) fn_sig
               ge tge f tf.
Proof (funct_ptr_translated Hfsim).

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\
             fundef_weak_lsim
               (@common_fundef_dec function) fn_sig
               (@common_fundef_dec function) fn_sig
               ge tge f tf.
Proof (functions_translated Hfsim).

Lemma find_function_translated:
  forall ros rs fd rs',
  find_function ge ros rs = Some fd ->
  regset_lessdef rs rs' ->
  exists tfd, find_function tge ros rs' = Some tfd /\
              fundef_weak_lsim
               (@common_fundef_dec function) fn_sig
               (@common_fundef_dec function) fn_sig
                ge tge fd tfd.
Proof.
  unfold find_function; intros; destruct ros.
- specialize (H0 r). inv H0.
  apply functions_translated; auto.
  rewrite <- H2 in H; discriminate.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

Lemma sig_preserved:
  forall f tf,
    fundef_weak_lsim
      (@common_fundef_dec function) fn_sig
      (@common_fundef_dec function) fn_sig
      ge tge f tf ->
    funsig tf = funsig f.
Proof.
  intros. inv H. inv Hsig. unfold common_fundef_dec in *.
  destruct f, tf; simpl in *; auto.
Qed.

Inductive match_stackframes (es es':list stackframe): list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes es es' es es'
  | match_stackframes_normal: forall stk stk' res sp pc rs rs' f,
      match_stackframes es es' stk stk' ->
      regset_lessdef rs rs' ->
      match_stackframes es es'
        (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
        (Stackframe res (transf_function f) (Vptr sp Int.zero) pc rs' :: stk')
  | match_stackframes_tail: forall stk stk' res sp pc rs f,
      match_stackframes es es' stk stk' ->
      is_return_spec f pc res ->
      f.(fn_stacksize) = 0 ->
      match_stackframes es es'
        (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
        stk'.

Inductive match_states (es es':list stackframe): state -> state -> Prop :=
  | match_states_normal:
      forall s sp pc rs m s' rs' m' f
             (STACKS: match_stackframes es es' s s')
             (RLD: regset_lessdef rs rs')
             (MLD: Mem.extends m m'),
      match_states es es'
                   (State s f (Vptr sp Int.zero) pc rs m)
                   (State s' (transf_function f) (Vptr sp Int.zero) pc rs' m')
  | match_states_return:
      forall s v m s' v' m',
      match_stackframes es es' s s' ->
      Val.lessdef v v' ->
      Mem.extends m m' ->
      match_states es es'
                   (Returnstate s v m)
                   (Returnstate s' v' m')
  | match_states_interm:
      forall s sp pc rs m s' m' f r v'
             (STACKS: match_stackframes es es' s s')
             (MLD: Mem.extends m m'),
      is_return_spec f pc r ->
      f.(fn_stacksize) = 0 ->
      Val.lessdef (rs#r) v' ->
      match_states es es'
                   (State s f (Vptr sp Int.zero) pc rs m)
                   (Returnstate s' v' m').

Inductive match_call (es es':list stackframe): state -> state -> Prop :=
  | match_states_call:
      forall s f args m s' f' args' m',
      match_stackframes es es' s s' ->
      fundef_weak_lsim
        (common_fundef_dec (F:=function)) fn_sig
        (common_fundef_dec (F:=function)) fn_sig
        ge tge f f' ->
      Val.lessdef_list args args' ->
      Mem.extends m m' ->
      match_call es es'
                 (Callstate s f args m)
                 (Callstate s' f' args' m')
.

Inductive match_return (es es':list stackframe): state -> state -> Prop :=
  | match_return_intro:
      forall v m v' m',
      match_stackframes es es' es es' ->
      Val.lessdef v v' ->
      Mem.extends m m' ->
      match_return es es'
                   (Returnstate es v m)
                   (Returnstate es' v' m').

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
  forall es es' s1 t s2, step ge s1 t s2 ->
  forall s1' (MS: match_states es es' s1 s1') (NMR: ~ match_return es es' s1 s1'),
  (exists s2', step tge s1' t s2' /\ (match_states es es' s2 s2' \/ match_call es es' s2 s2')) \/
  (measure s2 < measure s1 /\ t = E0 /\ (match_states es es' s2 s1' \/ match_call es es' s2 s1'))%nat.
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
  apply eval_operation_preserved. exact symbols_preserved.
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
  apply eval_addressing_preserved. exact symbols_preserved. eauto.
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
  apply eval_addressing_preserved. exact symbols_preserved. eauto.
  destruct a; simpl in H1; try discriminate.
  left. econstructor; eauto.

(* call *)
  exploit find_function_translated; eauto. intros [fd' [Hfd' FIND']].  
  TransfInstr.
(* call turned tailcall *)
  assert ({ m'' | Mem.free m' sp0 0 (fn_stacksize (transf_function f)) = Some m''}).
    apply Mem.range_perm_free. rewrite stacksize_preserved. rewrite H7. 
    red; intros; omegaContradiction.
  destruct X as [m'' FREE].
  left. exists (Callstate s' fd' (rs'##args) m''); split.
  eapply exec_Itailcall; eauto. apply sig_preserved. auto.
  right. constructor; auto. eapply match_stackframes_tail; eauto. apply regset_get_list; auto.
  eapply Mem.free_right_extends; eauto.
  rewrite stacksize_preserved. rewrite H7. intros. omegaContradiction.
(* call that remains a call *)
  left. exists (Callstate (Stackframe res (transf_function f) (Vptr sp0 Int.zero) pc' rs' :: s')
                          fd' (rs'##args) m'); split.
  eapply exec_Icall; eauto. apply sig_preserved. auto. 
  right. constructor; auto. constructor; auto. apply regset_get_list; auto.

(* tailcall *) 
  exploit find_function_translated; eauto. intros [fd' [Hfd' FIND']].
  exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
  TransfInstr.
  left. exists (Callstate s' fd' (rs'##args) m'1); split.
  eapply exec_Itailcall; eauto. apply sig_preserved. auto.
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
  exact symbols_preserved. exact varinfo_preserved.
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
(* match_return *)
  contradict NMR. repeat (constructor; auto).
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
  intros [[s2' [Hs2' Hmatch']]|[Hmeasure [Hevt Hmatch']]].
  - eexists. eexists. exists tt.
    split; [left; apply plus_one; eauto|].
    split; [simpl; auto|].
    split; [destruct Hmatch' as [Hmatch'|Hmatch']; inv Hmatch'; auto|].
    destruct Hmatch' as [Hmatch'|Hmatch'].
    + constructor. right. apply CIH. constructor; auto.
      * eapply sound_past_step; eauto.
      * eapply sound_past_step; eauto.
    + inv Hmatch'. eapply _state_lsim_or_csim_csim; eauto.
      { apply mrelT_ops_extends_lessdef_list. auto. }
      intros. right. destruct mrel2. apply CIH. constructor; auto.
      subst. constructor; auto.
  - subst. eexists. eexists. exists tt.
    split.
    { right. split. apply star_refl.
      instantiate (1 := i). admit. (* index *)
    }
    split; [admit|]. (* index *)
    split; [destruct Hmatch' as [Hmatch'|Hmatch']; inv Hmatch'; auto|].
    destruct Hmatch' as [Hmatch'|Hmatch'].
    + constructor. right. apply CIH. constructor; auto.
      * eapply sound_past_step; eauto.
    + inv Hmatch'. eapply _state_lsim_or_csim_csim; eauto.
      { apply mrelT_ops_extends_lessdef_list. auto. }
      intros. right. destruct mrel2. apply CIH. constructor; auto.
      subst. constructor; auto.
Grab Existential Variables.
  { apply i. }
Qed.

Lemma transf_function_lsim f:
  function_lsim mrelT_ops_extends fprog ftprog f (transf_function f).
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

(* internal call *)
  simpl in *. exploit Mem.alloc_extends; eauto.
    instantiate (1 := 0). omega.
    instantiate (1 := fn_stacksize f). omega.
  intros [m'1 [ALLOC EXT]].
  assert (fn_stacksize (transf_function f) = fn_stacksize f /\
          fn_entrypoint (transf_function f) = fn_entrypoint f /\
          fn_params (transf_function f) = fn_params f).
    unfold transf_function. destruct (zeq (fn_stacksize f) 0 && Compopts.eliminate_tailcalls tt); auto.
  destruct H as [EQ1 [EQ2 EQ3]].
  rewrite EQ1, ALLOC. simpl. split; auto.
  constructor. destruct mrel_entry.
  exploit match_states_state_lsim; eauto.
  constructor.
  - rewrite EQ2, EQ3. repeat (constructor; auto).
    apply regset_init_regs.
    eapply mrelT_ops_extends_lessdef_list.
    instantiate (1 := tt). auto.
  - eapply sound_past_step; eauto.
  - eapply sound_past_step; eauto.
    constructor. rewrite EQ1, ALLOC. auto.
Qed.

End FUTURE.

Lemma Tailcall_program_lsim:
  program_lsim
    (@common_fundef_dec function) fn_sig
    (@common_fundef_dec function) fn_sig
    (@Errors.OK _)
    (function_lsim mrelT_ops_extends)
    prog tprog.
Proof.
  generalize transf_function_lsim.
  destruct prog as [defs main], tprog as [tdefs tmain]. clear prog tprog.
  unfold transf_program, transform_program in TRANSF.
  inv TRANSF. intro Hlsim. constructor; simpl; auto.
  revert Hlsim.
  generalize defs at 1 2 3 as fdefs. revert defs.
  induction defs; simpl; intros fdefs Hlsim; simpl.
  { constructor. }
  { destruct a. destruct g.
    { constructor; simpl in *.
      { split; auto. constructor.
        destruct f; simpl in *.
        { eapply globfun_lsim_i; eauto;
          unfold common_fundef_dec; eauto.
          split; auto. repeat intro.
          apply Hlsim; auto.
          unfold transf_function. destruct (zeq (fn_stacksize f) 0 && Compopts.eliminate_tailcalls tt); simpl; auto.
        }
        { eapply globfun_lsim_e; eauto;
          unfold common_fundef_dec; eauto.
        }
      }
      { apply IHdefs; auto. }
    }
    { constructor; simpl in *.
      { split; auto. repeat constructor.
        unfold transf_globvar. simpl. destruct v; auto.
      }
      apply IHdefs; auto.
    }
  }
Qed.

End PRESERVATION.
