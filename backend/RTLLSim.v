Require Import RelationClasses.
Require Import Coqlib.
Require Import paco.
Require Import WFType.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import LinkerSpecification.
Require Import ProgramLSim.
Require Import ValueAnalysis_linker.

Set Implicit Arguments.

(* common definitions/lemmas on RTL *)

Definition transf_V := fun (tt:unit) => Errors.OK tt.

Lemma initial_state_unique p s1 s2
      (H1: initial_state p s1)
      (H2: initial_state p s2):
  s1 = s2.
Proof.
  inv H1. inv H2. unfold ge, ge0 in *.
  rewrite H in H1. inv H1. rewrite H0 in H5. inv H5. rewrite H3 in H6. inv H6.
  auto.
Qed.

Lemma transf_efT_sigT:
  forall (ef_src : efT Language_RTL) (ef_tgt : efT Language_RTL),
    Errors.OK ef_src = Errors.OK ef_tgt ->
    id (EF_sig (efT Language_RTL) ef_src) =
    EF_sig (efT Language_RTL) ef_tgt.
Proof. intros. inv H. auto. Qed.

Lemma Fundef_sig_RTL f: Fundef_sig (Fundef_common F_RTL) f = RTL.funsig f.
Proof. unfold Fundef_sig, Fundef_dec. simpl. destruct f; auto. Qed.

Section FUTURE.

Variable (fprog ftprog:program).
Hypothesis (Hfsim: @program_weak_lsim Language_RTL Language_RTL id (@Errors.OK _) transf_V
                                      fprog ftprog).

Let globfun_weak_lsim :=
  @globfun_lsim Language_RTL Language_RTL id (@Errors.OK _)
                (fun _ _ _ _ => True)
                fprog ftprog.

Let ge := Genv.globalenv fprog.
Let tge := Genv.globalenv ftprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (symbols_preserved transf_efT_sigT Hfsim).

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. exploit varinfo_preserved; try exact transf_efT_sigT; try exact Hfsim.
  instantiate (1 := b). unfold ge, tge, fundef. simpl in *.
  match goal with
    | [|- context[match ?v1 with | Some _ => match ?v2 with | Some _ => _ | None => _ end | None => _ end]] =>
      destruct v1, v2; intros; auto; inv H
  end.
  destruct g0; auto.
Qed.

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\
             fundef_weak_lsim Language_RTL Language_RTL id ge tge f tf.
Proof (funct_ptr_translated transf_efT_sigT Hfsim).

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\
             fundef_weak_lsim Language_RTL Language_RTL id ge tge f tf.
Proof (functions_translated transf_efT_sigT Hfsim).

Lemma find_function_translated_Renumber:
  forall ros rs fd,
  find_function ge ros rs = Some fd ->
  exists tfd, find_function tge ros rs = Some tfd /\
              fundef_weak_lsim Language_RTL Language_RTL id ge tge fd tfd.
Proof.
  unfold find_function; intros; destruct ros.
- apply functions_translated; auto.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

Lemma find_function_translated_CSE:
  forall ros rs fd rs',
  find_function ge ros rs = Some fd ->
  CSEproof.regs_lessdef rs rs' ->
  exists tfd, find_function tge ros rs' = Some tfd /\
              fundef_weak_lsim Language_RTL Language_RTL id ge tge fd tfd.
Proof.
  unfold find_function; intros; destruct ros.
- specialize (H0 r). inv H0.
  apply functions_translated; auto.
  rewrite <- H2 in H; discriminate.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

Lemma find_function_translated_Tailcall:
  forall ros rs fd rs',
  find_function ge ros rs = Some fd ->
  Tailcallproof.regset_lessdef rs rs' ->
  exists tfd, find_function tge ros rs' = Some tfd /\
              fundef_weak_lsim Language_RTL Language_RTL id ge tge fd tfd.
Proof.
  unfold find_function; intros; destruct ros.
- specialize (H0 r). inv H0.
  apply functions_translated; auto.
  rewrite <- H2 in H; discriminate.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

Lemma find_function_translated_Constprop:
  forall ros rs fd rs',
  find_function ge ros rs = Some fd ->
  Constpropproof.regs_lessdef rs rs' ->
  exists tfd, find_function tge ros rs' = Some tfd /\
              fundef_weak_lsim Language_RTL Language_RTL id ge tge fd tfd.
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
    fundef_weak_lsim Language_RTL Language_RTL id ge tge f tf ->
    funsig tf = funsig f.
Proof.
  intros. inv H. inv Hsig. rewrite ? Fundef_sig_RTL in Hsig0. auto.
Qed.

End FUTURE.

Record mrelT_opsT (t:Type): Type := mkmrelT_opsT {
  sem :> t -> forall (p1 p2:program) (i:WF.t) (s1 s2:state), Prop;
  sem_value :> t -> forall (v1 v2:val), Prop;
  le: t -> t -> Prop;
  le_public: t -> t -> Prop
}.

Record mrelT_propsT (t:Type) (ops:mrelT_opsT t): Prop := mkmrelT_propsT {
  le_preorder: PreOrder ops.(le);
  le_public_preorder: PreOrder ops.(le_public);
  le_public_le:
    forall mrel1 mrel2 (Hle_public: ops.(le_public) mrel1 mrel2),
      ops.(le) mrel1 mrel2;
  sem_value_int:
    forall mrel i v (H: ops.(sem_value) mrel (Vint i) v),
      v = Vint i;
  Hmrel_i_init:
    forall p1 p2 s1 s2
           (Hp: @program_weak_lsim Language_RTL Language_RTL id (@Errors.OK _) transf_V
                                   p1 p2)
           (H1: initial_state p1 s1)
           (H2: initial_state p2 s2),
    exists mrel_init i_init,
      ops.(sem) mrel_init p1 p2 i_init s1 s2;
  Hexternal_call:
    forall p1 p2 s1 s2 cs1 cs2 ef args1 args2 m1 m2 evt s1' res1 m1' mrel i
           (Hp: @program_weak_lsim Language_RTL Language_RTL id (@Errors.OK _) transf_V
                                   p1 p2)
           (Hs1: s1 = Callstate cs1 (External ef) args1 m1)
           (Hs2: s2 = Callstate cs2 (External ef) args2 m2)
           (Hs1': s1' = Returnstate cs1 res1 m1')
           (Hmrel: ops.(sem) mrel p1 p2 i s1 s2)
           (Hs2: step (Genv.globalenv p1) s1 evt s1')
           (Hargs: list_forall2 (ops.(sem_value) mrel) args1 args2),
    exists mrel' i' s2' res2 m2',
      s2' = Returnstate cs2 res2 m2' /\
      step (Genv.globalenv p2) s2 evt s2' /\
      ops.(sem) mrel' p1 p2 i' s1' s2' /\
      ops.(sem_value) mrel' res1 res2 /\
      ops.(le_public) mrel mrel'
}.

Section LSIM.

Variable (mrelT:Type).
Variable (mrelT_ops:mrelT_opsT mrelT).

Variable (fprog_src fprog_tgt:program).

Let ge_src := Genv.globalenv fprog_src.
Let ge_tgt := Genv.globalenv fprog_tgt.

Section STATE_LSIM.

Variable (cs_entry_src cs_entry_tgt:list stackframe).
Variable (mrel_entry:mrelT).

Inductive _state_lsim_or_csim
          (state_lsim: mrelT -> WF.t -> state -> state -> Prop)
          (mrel:mrelT) (i:WF.t) (st_src st_tgt:state): Prop :=
| _state_lsim_or_csim_lsim
    (Hlsim: state_lsim mrel i st_src st_tgt)
| _state_lsim_or_csim_csim
    stack_src fundef_src args_src mem_src
    (Hst_src: st_src = Callstate stack_src fundef_src args_src mem_src)
    stack_tgt fundef_tgt args_tgt mem_tgt
    (Hst_tgt: st_tgt = Callstate stack_tgt fundef_tgt args_tgt mem_tgt)
    (Hfundef: fundef_weak_lsim Language_RTL Language_RTL id ge_src ge_tgt fundef_src fundef_tgt)
    (Hargs: list_forall2 (mrelT_ops.(sem_value) mrel) args_src args_tgt)
    (Hmrel: mrelT_ops.(sem) mrel fprog_src fprog_tgt i st_src st_tgt)
    (Hreturn:
       forall mrel2 i2 st2_src st2_tgt mem2_src mem2_tgt vres_src vres_tgt
              (Hvres: mrelT_ops.(sem_value) mrel2 vres_src vres_tgt)
              (Hst2_src: st2_src = Returnstate stack_src vres_src mem2_src)
              (Hst2_tgt: st2_tgt = Returnstate stack_tgt vres_tgt mem2_tgt)
              (Hsound_src: sound_state_ext fprog_src st2_src)
              (Hsound_tgt: sound_state_ext fprog_tgt st2_tgt)
              (Hmrel2_le: mrelT_ops.(le_public) mrel mrel2)
              (Hst2_mem: mrelT_ops.(sem) mrel2 fprog_src fprog_tgt i2 st2_src st2_tgt),
         state_lsim mrel2 i2 st2_src st2_tgt)
.

Inductive _state_lsim
          (state_lsim: mrelT -> WF.t -> state -> state -> Prop)
          (mrel:mrelT) (i:WF.t) (st_src st_tgt:state): Prop :=
| _state_lsim_term
    rval
    (Hst_src: final_state st_src rval)
    (Hst_tgt: final_state st_tgt rval)

| _state_lsim_return
    (Hsound_src: sound_state_ext fprog_src st_src)
    (Hsound_tgt: sound_state_ext fprog_tgt st_tgt)
    val_src mem_src (Hst_src: st_src = Returnstate cs_entry_src val_src mem_src)
    val_tgt mem_tgt (Hst_tgt: st_tgt = Returnstate cs_entry_tgt val_tgt mem_tgt)
    (Hval: mrelT_ops.(sem_value) mrel val_src val_tgt)
    (Hmem: mrelT_ops.(sem) mrel fprog_src fprog_tgt i st_src st_tgt)
    (Hmrel_le_public: mrelT_ops.(le_public) mrel_entry mrel)

| _state_lsim_step
    (Hnfinal: forall r, ~ final_state st_src r)
    (Hsound_src: sound_state_ext fprog_src st_src)
    (Hsound_tgt: sound_state_ext fprog_tgt st_tgt)
    (Hpreserve:
       forall evt st2_src (Hst2_src: step ge_src st_src evt st2_src),
         exists i2 st2_tgt (mrel2:mrelT),
           (plus step ge_tgt st_tgt evt st2_tgt \/
            star step ge_tgt st_tgt evt st2_tgt /\ WF.rel i2 i) /\
           mrelT_ops.(le) mrel mrel2 /\
           mrelT_ops.(sem) mrel2 fprog_src fprog_tgt i2 st2_src st2_tgt /\
           _state_lsim_or_csim state_lsim mrel2 i2 st2_src st2_tgt)
.
Hint Constructors _state_lsim.

Lemma state_lsim_mon: monotone4 _state_lsim.
Proof.
  repeat intro; destruct IN; eauto.
  - eapply _state_lsim_step; eauto.
    intros. exploit Hpreserve; eauto. intros [i2 [st2_tgt [mrel2 [Hstep [Hle [Hmrel Hsim]]]]]].
    eexists. eexists. eexists. repeat (split; eauto).
    inv Hsim.
    + apply _state_lsim_or_csim_lsim. eauto.
    + eapply _state_lsim_or_csim_csim; eauto.
Qed.

Definition state_lsim: _ -> _ -> _ -> _ -> Prop :=
  paco4 _state_lsim bot4.

End STATE_LSIM.

Inductive function_lsim (func_src func_tgt:function): Prop :=
| function_lsim_intro
    (Hlsim:
       forall
         mrel_entry mem_entry_src mem_entry_tgt
         cs_entry_src cs_entry_tgt
         args_src args_tgt
         st_src st_tgt
         i
         (Hmrel_entry: mrelT_ops.(sem) mrel_entry fprog_src fprog_tgt i st_src st_tgt)
         (Hargs: list_forall2 (mrelT_ops.(sem_value) mrel_entry) args_src args_tgt)
         (Hst_src: st_src = (Callstate cs_entry_src (Internal func_src) args_src mem_entry_src))
         (Hst_tgt: st_tgt = (Callstate cs_entry_tgt (Internal func_tgt) args_tgt mem_entry_tgt))
         (Hsound_src: sound_state_ext fprog_src st_src)
         (Hsound_tgt: sound_state_ext fprog_tgt st_tgt),
         state_lsim
           cs_entry_src cs_entry_tgt mrel_entry
           mrel_entry i
           (Callstate cs_entry_src (Internal func_src) args_src mem_entry_src)
           (Callstate cs_entry_tgt (Internal func_tgt) args_tgt mem_entry_tgt))
.

End LSIM.
Hint Constructors _state_lsim.
Hint Resolve state_lsim_mon: paco.
