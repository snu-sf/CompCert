Require Import Coqlib Coqlib_linker.
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
Require Import ProgramLSim FunctionLSim.

Set Implicit Arguments.

Section ADEQUACY.

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
Hypothesis transf_sigT_main: transf_sigT lang_src.(signature_main) = lang_tgt.(signature_main).

Variable (mrelT:Type).
Variable (mrelT_ops:mrelT_opsT lang_src lang_tgt mrelT).
Hypothesis (mrelT_props:mrelT_propsT transf_sigT transf_efT transf_vT mrelT_ops).

Variable (prog_src:lang_src.(progT)).
Variable (prog_tgt:lang_tgt.(progT)).
Hypothesis
  (Hsim: @program_lsim lang_src lang_tgt transf_sigT transf_efT transf_vT
                       (function_lsim transf_sigT transf_efT mrelT_ops)
                       prog_src prog_tgt).

Lemma Hweak_sim:
  @program_weak_lsim lang_src lang_tgt transf_sigT transf_efT transf_vT
                     prog_src prog_tgt.
Proof. eapply program_lsim_aux_le; eauto. Qed.
Hint Resolve Hweak_sim.

Inductive match_stackframes: forall (height:nat) (mrel:mrelT) (es_src:lang_src.(contT)) (es_tgt:lang_tgt.(contT)), Prop :=
| match_stackframes_nil mrel_init:
    match_stackframes 0 mrel_init lang_src.(empty_cont) lang_tgt.(empty_cont)
| match_stackframes_cons
    height ps_src ps_tgt es_src es_tgt
    emrel mrel
    (Hp: match_stackframes height emrel ps_src ps_tgt)
    (Hmrel_le: mrelT_ops.(le) emrel mrel)
    (Hreturn:
       forall rmrel ri st_src st_tgt mem_src mem_tgt vres_src vres_tgt
              (Hvres: mrelT_ops.(sem_value) rmrel vres_src vres_tgt)
              (Hst_src: st_src = lang_src.(mkReturnstate) es_src vres_src mem_src)
              (Hst_tgt: st_tgt = lang_tgt.(mkReturnstate) es_tgt vres_tgt mem_tgt)
              (Hrmrel_le: mrelT_ops.(le_public) mrel rmrel)
              (Hst_mem: mrelT_ops.(sem) rmrel prog_src prog_tgt ri st_src st_tgt),
         state_lsim transf_sigT transf_efT mrelT_ops prog_src prog_tgt ps_src ps_tgt emrel rmrel ri st_src st_tgt):
    match_stackframes (S height) mrel es_src es_tgt
.

Inductive match_states (i:WF.t) (st_src:lang_src.(stateT)) (st_tgt:lang_tgt.(stateT)): Prop :=
| match_states_intro
    height es_src es_tgt
    emrel mrel
    (Hp: match_stackframes height emrel es_src es_tgt)
    (Hmrel_le: mrelT_ops.(le) emrel mrel)
    (Hsim: state_lsim transf_sigT transf_efT mrelT_ops prog_src prog_tgt es_src es_tgt emrel mrel i st_src st_tgt)
.

Lemma program_sim_forward_simulation:
  forward_simulation (lang_src.(semantics) prog_src) (lang_tgt.(semantics) prog_tgt).
Proof.
  eapply (Forward_simulation
            (lang_src.(semantics) prog_src) (lang_tgt.(semantics) prog_tgt)
            WF.wf match_states).
  { (* initial *)
    intros. destruct H as [b [f [m0 [Hm0 [Hb [Hf [Hsig ?]]]]]]]. subst.
    exploit funct_ptr_translated; eauto. intros [tf [A B]].
    assert (Hinitial_tgt: initial_state lang_tgt prog_tgt (lang_tgt.(mkCallstate) lang_tgt.(empty_cont) tf nil m0)).
    { exists b. exists tf. exists m0.
      split. eapply program_lsim_init_mem_match; eauto.
      split. replace (prog_main prog_tgt) with (prog_main prog_src).
        erewrite symbols_preserved; eauto. auto.
        destruct Hsim as [_ Hmain]. auto.
      repeat (split; auto).
      rewrite <- transf_sigT_main, <- Hsig. apply sig_preserved in B; auto.
    }
    exploit (mrelT_props.(Hmrel_i_init)); eauto.
    { eexists. eexists. eexists. eauto. }
    intros [mrel_init [i_init Hinitial]].
    exists i_init. exists (lang_tgt.(mkCallstate) lang_tgt.(empty_cont) tf nil m0). split; auto.
    econstructor.
    { apply match_stackframes_nil. }
    { destruct mrelT_props. reflexivity. }
    exploit funct_ptr_translated'; try exact transf_efT_sigT; eauto.
    intros [tf' [Htf' Hfundef_sim]]. rewrite A in Htf'. symmetry in Htf'. inv Htf'.
    inv Hfundef_sim.
    destruct (Fundef_dec (fundefT lang_src) f) as [f_src|ef_src] eqn:Hfundef_src,
             (Fundef_dec (fundefT lang_tgt) tf) as [f_tgt|ef_tgt] eqn:Hfundef_tgt;
    try (inv Hsim0; fail).
    - exploit Hsim0; try reflexivity. unfold F_future_lsim. intros.
      destruct H as [Hfunction_sim Hfunction_sig].
      exploit Hfunction_sim; eauto.
      intro X. inv X. eapply Hlsim; eauto. constructor.
    - inv Hsim0. pfold. constructor.
      { intros r Hr. inv Hr. exploit Hfinal_not_call; eauto. }
      intros. exploit (mrelT_props.(Hexternal_call)); eauto.
      { constructor. }
      intros [res [m2 [s2' [res' [m2' [mrel2 [i2 [? [? [Hst2_tgt [Hmrel2 [Hmrel2_val Hmrel2_le]]]]]]]]]]]].
      exists i2. exists s2'. exists mrel2.
      split; [left; apply plus_one; auto|].
      split; [apply mrelT_props.(le_public_le); auto|].
      split; auto. subst. econstructor. left.
      pfold. eapply _state_lsim_return; eauto.
  }
 { (* final *)
    simpl. intros. inv H0. inv H. punfold Hsim0. inv Hsim0.
    - inv Hst_src. apply HmkReturnstate_inj in H. destruct H as [? [? ?]]. subst.
      inv H0. auto.
    - apply HmkReturnstate_inj in Hst_src. destruct Hst_src as [? [? ?]]. subst.
      revert height emrel Hmrel_le Hmrel_le_public Hp.
      refine (strong_nat_ind _ _). intros height IHheight emrel Hmrel_le Hmrel_le_public Hp.
      inversion Hp; symmetry in H0; subst.
      { exploit (mrelT_props.(sem_value_int)); eauto. intro. subst.
        econstructor. eauto.
      }
      { exploit Hreturn; eauto. intro Hsim'.
        punfold Hsim'. inv Hsim'.
        { inv Hst_src. apply HmkReturnstate_inj in H. destruct H as [? [? ?]]. subst.
          inv Hst_tgt. apply HmkReturnstate_inj in H1. destruct H1 as [? [? ?]]. subst.
          inv H0. econstructor. eauto.
        }
        { apply HmkReturnstate_inj in Hst_src. destruct Hst_src as [? [? ?]]. subst.
          apply HmkReturnstate_inj in Hst_tgt. destruct Hst_tgt as [? [? ?]]. subst.
          assert (Hle: mrelT_ops.(le) emrel0 mrel).
          { destruct mrelT_props. etransitivity; eauto. }
          eauto.
        }
        { exfalso. eapply Hnfinal. econstructor. eauto. }
      }
    - exfalso. eapply Hnfinal. econstructor. eauto.
  }
  { (* progress & preservation *)
    intros. inv H0.
    revert height i s2 es_src es_tgt emrel mrel Hp Hmrel_le Hsim0.
    refine (strong_nat_ind _ _). intros height IHheight. intros.
    punfold Hsim0. inv Hsim0.
    - (* term *)
      inv Hst_src. exfalso. eapply Hfinal_not_progress.
      eexists. eexists. eexists. apply H.
    - (* return *)
      inversion Hp; subst.
      { exfalso. eapply Hfinal_not_progress.
        eexists. eexists. eexists. apply H.
      }
      assert (Hmrel_le': mrelT_ops.(le) emrel0 mrel).
      { destruct mrelT_props. etransitivity; eauto. }
      exploit Hreturn; eauto.
    - (* step *)
      exploit Hpreserve; eauto. intros [i2 [st2_tgt [mrel2 [Hstep2 [Hle2 [Hmrel2 Hsim2]]]]]].
      assert (Hmrel2_le: mrelT_ops.(le) emrel mrel2).
      { destruct mrelT_props. etransitivity; eauto. }
      exists i2. exists st2_tgt. split; auto.
      inv Hsim2.
      { pclearbot. econstructor; eauto. }
      econstructor.
      { eapply match_stackframes_cons; eauto.
        instantiate (1 := cont_tgt). instantiate (1 := cont_src). intros. subst.
        exploit Hreturn; eauto. intro Hsim2. pclearbot. eauto.
      }
      { destruct mrelT_props. reflexivity. }
      inv Hfundef.
      destruct (Fundef_dec (fundefT lang_src) fundef_src) as [f_src|ef_src] eqn:Hfundef_src,
               (Fundef_dec (fundefT lang_tgt) fundef_tgt) as [f_tgt|ef_tgt] eqn:Hfundef_tgt;
      try (inv Hsim0; fail).
      + destruct Hsim0 as [Hf_sig [b [Hsrc Htgt]]].
        exploit funct_ptr_translated'; try exact transf_efT_sigT; eauto.
        intros [tf [Htf Hfundef_sim]]. unfold Genv.find_funct_ptr in Htf. rewrite Htgt in Htf. symmetry in Htf. inv Htf.
        inv Hfundef_sim. rewrite Hfundef_src, Hfundef_tgt in *.
        exploit Hsim0; try reflexivity. unfold F_future_lsim. intros.
        destruct H0 as [Hfunction_sim Hfunction_sig].
        exploit Hfunction_sim; eauto.
        intro X. inv X. eapply Hlsim; eauto.
      + pfold. constructor.
        { intros ? Hfinal. inv Hfinal. exploit Hfinal_not_call; eauto. }
        intros. exploit (mrelT_props.(Hexternal_call)); eauto.
        intros [res [m3 [s3' [res' [m3' [mrel3 [i3 [? [? [Hst3_tgt [Hmrel3 [Hmrel3_val Hmrel3_le]]]]]]]]]]]].
        exists i3. exists s3'. exists mrel3.
        split; [left; apply plus_one; auto|].
        split; [apply mrelT_props.(le_public_le); auto|].
        split; auto. subst. econstructor. left.
        pfold. eapply _state_lsim_return; eauto.
  }
  { eapply symbols_preserved; eauto. }
Qed.

End ADEQUACY.
