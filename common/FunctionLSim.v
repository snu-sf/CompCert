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
Require Import Language Linker.
Require Import ProgramLSim.

Set Implicit Arguments.

Section LSIM.

Variable (lang_src lang_tgt:Language_ext).

Let sigT_src := lang_src.(sigT).
Let fT_src := lang_src.(fT).
Let efT_src := lang_src.(efT).
Let fundefT_src := lang_src.(fundefT).
Let vT_src := lang_src.(vT).

Let f_sig_src := fT_src.(F_sig).
Let ef_sig_src := efT_src.(EF_sig).
Let fd_sig_src := fundefT_src.(Fundef_sig).
Let ef_dec_src := efT_src.(EF_dec).
Let fundef_dec_src := fundefT_src.(Fundef_dec).
Let v_dec_src := vT_src.(V_dec).

Let sigT_tgt := lang_tgt.(sigT).
Let fT_tgt := lang_tgt.(fT).
Let efT_tgt := lang_tgt.(efT).
Let fundefT_tgt := lang_tgt.(fundefT).
Let vT_tgt := lang_tgt.(vT).

Let f_sig_tgt := fT_tgt.(F_sig).
Let ef_sig_tgt := efT_tgt.(EF_sig).
Let fd_sig_tgt := fundefT_tgt.(Fundef_sig).
Let ef_dec_tgt := efT_tgt.(EF_dec).
Let fundef_dec_tgt := fundefT_tgt.(Fundef_dec).
Let v_dec_tgt := vT_tgt.(V_dec).

Variable (transf_sigT: forall (ef:sigT_src), sigT_tgt).
Variable (transf_efT: forall (ef:efT_src), Errors.res efT_tgt).
Variable (transf_vT: forall (v:vT_src), Errors.res vT_tgt).
Hypothesis transf_efT_sigT: forall ef_src ef_tgt (H: transf_efT ef_src = Errors.OK ef_tgt), transf_sigT (ef_sig_src ef_src) = ef_sig_tgt ef_tgt.

Record mrelT_opsT (t:Type): Type := mkmrelT_opsT {
  sem :> t -> forall (p_src:lang_src.(progT)) (p_tgt:lang_tgt.(progT)) (i:WF.t) (s1:lang_src.(stateT)) (s2:lang_tgt.(stateT)), Prop;
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
           (Hp: @program_weak_lsim lang_src lang_tgt transf_sigT transf_efT transf_vT
                                   p1 p2)
           (H1: lang_src.(initial_state) p1 s1)
           (H2: lang_tgt.(initial_state) p2 s2),
    exists mrel_init i_init,
      ops.(sem) mrel_init p1 p2 i_init s1 s2;
  Hexternal_call:
    forall p1 p2 s1 s2 es1 es2 fd1 fd2 ef1 ef2 args1 args2 m1 m2 evt s1' mrel i
           (Hp: @program_weak_lsim lang_src lang_tgt transf_sigT transf_efT transf_vT
                                   p1 p2)
           (Hs1: s1 = lang_src.(mkCallstate) es1 fd1 args1 m1)
           (Hs2: s2 = lang_tgt.(mkCallstate) es2 fd2 args2 m2)
           (Hfd1: fundef_dec_src fd1 = inr ef1)
           (Hfd2: fundef_dec_tgt fd2 = inr ef2)
           (Hef: transf_efT ef1 = Errors.OK ef2)
           (Hmrel: ops.(sem) mrel p1 p2 i s1 s2)
           (Hs2: lang_src.(step) (Genv.globalenv p1) s1 evt s1')
           (Hargs: list_forall2 (ops.(sem_value) mrel) args1 args2),
    exists res1 m1' s2' res2 m2' mrel' i',
      s1' = lang_src.(mkReturnstate) es1 res1 m1' /\
      s2' = lang_tgt.(mkReturnstate) es2 res2 m2' /\
      lang_tgt.(step) (Genv.globalenv p2) s2 evt s2' /\
      ops.(sem) mrel' p1 p2 i' s1' s2' /\
      ops.(sem_value) mrel' res1 res2 /\
      ops.(le_public) mrel mrel'
}.

Variable (mrelT:Type).
Variable (mrelT_ops:mrelT_opsT mrelT).

Variable (fprog_src:lang_src.(progT)).
Variable (fprog_tgt:lang_tgt.(progT)).

Let ge_src := Genv.globalenv fprog_src.
Let ge_tgt := Genv.globalenv fprog_tgt.

Section STATE_LSIM.

Variable (es_src:lang_src.(contT)).
Variable (es_tgt:lang_tgt.(contT)).
Variable (mrel_entry:mrelT).

Inductive _state_lsim_or_csim
          (state_lsim: mrelT -> WF.t -> lang_src.(stateT) -> lang_tgt.(stateT) -> Prop)
          (mrel:mrelT) (i:WF.t) (st_src:lang_src.(stateT)) (st_tgt:lang_tgt.(stateT)): Prop :=
| _state_lsim_or_csim_lsim
    (Hlsim: state_lsim mrel i st_src st_tgt)
| _state_lsim_or_csim_csim
    cont_src fundef_src args_src mem_src
    (Hst_src: st_src = lang_src.(mkCallstate) cont_src fundef_src args_src mem_src)
    cont_tgt fundef_tgt args_tgt mem_tgt
    (Hst_tgt: st_tgt = lang_tgt.(mkCallstate) cont_tgt fundef_tgt args_tgt mem_tgt)
    (Hfundef: globfun_weak_lsim lang_src lang_tgt transf_sigT ge_src ge_tgt fundef_src fundef_tgt)
    (Hargs: list_forall2 (mrelT_ops.(sem_value) mrel) args_src args_tgt)
    (Hmrel: mrelT_ops.(sem) mrel fprog_src fprog_tgt i st_src st_tgt)
    (Hreturn:
       forall mrel2 i2 st2_src st2_tgt mem2_src mem2_tgt vres_src vres_tgt
              (Hvres: mrelT_ops.(sem_value) mrel2 vres_src vres_tgt)
              (Hst2_src: st2_src = lang_src.(mkReturnstate) cont_src vres_src mem2_src)
              (Hst2_tgt: st2_tgt = lang_tgt.(mkReturnstate) cont_tgt vres_tgt mem2_tgt)
              (Hmrel2_le: mrelT_ops.(le_public) mrel mrel2)
              (Hst2_mem: mrelT_ops.(sem) mrel2 fprog_src fprog_tgt i2 st2_src st2_tgt),
         state_lsim mrel2 i2 st2_src st2_tgt)
.

Inductive _state_lsim
          (state_lsim: mrelT -> WF.t -> lang_src.(stateT) -> lang_tgt.(stateT) -> Prop)
          (mrel:mrelT) (i:WF.t) (st_src:lang_src.(stateT)) (st_tgt:lang_tgt.(stateT)): Prop :=
| _state_lsim_term
    rval
    (Hst_src: lang_src.(final_state) st_src rval)
    (Hst_tgt: lang_tgt.(final_state) st_tgt rval)

| _state_lsim_return
    val_src mem_src (Hst_src: st_src = lang_src.(mkReturnstate) es_src val_src mem_src)
    val_tgt mem_tgt (Hst_tgt: st_tgt = lang_tgt.(mkReturnstate) es_tgt val_tgt mem_tgt)
    (Hval: mrelT_ops.(sem_value) mrel val_src val_tgt)
    (Hmem: mrelT_ops.(sem) mrel fprog_src fprog_tgt i st_src st_tgt)
    (Hmrel_le_public: mrelT_ops.(le_public) mrel_entry mrel)

| _state_lsim_step
    (Hnfinal: forall r, ~ lang_src.(final_state) st_src r)
    (Hpreserve:
       forall evt st2_src (Hst2_src: lang_src.(step) ge_src st_src evt st2_src),
         exists i2 st2_tgt (mrel2:mrelT),
           (plus lang_tgt.(step) ge_tgt st_tgt evt st2_tgt \/
            star lang_tgt.(step) ge_tgt st_tgt evt st2_tgt /\ WF.rel i2 i) /\
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

Inductive function_lsim (func_src:lang_src.(fT)) (func_tgt:lang_tgt.(fT)): Prop :=
| function_lsim_intro
    (Hlsim:
       forall
         mrel_entry mem_entry_src mem_entry_tgt
         es_src es_tgt
         fd_src fd_tgt
         args_src args_tgt
         st_src st_tgt
         i
         (Hmrel_entry: mrelT_ops.(sem) mrel_entry fprog_src fprog_tgt i st_src st_tgt)
         (Hfd_src: fundef_dec_src fd_src = inl func_src)
         (Hfd_tgt: fundef_dec_tgt fd_tgt = inl func_tgt)
         (Hargs: list_forall2 (mrelT_ops.(sem_value) mrel_entry) args_src args_tgt)
         (Hst_src: st_src = lang_src.(mkCallstate) es_src fd_src args_src mem_entry_src)
         (Hst_tgt: st_tgt = lang_tgt.(mkCallstate) es_tgt fd_tgt args_tgt mem_entry_tgt),
         state_lsim
           es_src es_tgt mrel_entry
           mrel_entry i
           st_src st_tgt)
.

End LSIM.
Hint Constructors _state_lsim.
Hint Resolve state_lsim_mon: paco.
