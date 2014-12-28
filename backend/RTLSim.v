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
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import LinkerSpecification.
Require Import ValueAnalysis_linker.
Require Import ProgramLSim RTLLSim.

Set Implicit Arguments.

Section GLOBAL_SIM.

Variable (mrelT:Type).
Variable (mrelT_ops:mrelT_opsT mrelT).
Hypothesis (mrelT_props:mrelT_propsT mrelT_ops).

Variable (prog_src prog_tgt:program).
Hypothesis
  (Hsim:
     program_lsim
       (@common_fundef_dec function) fn_sig
       (@common_fundef_dec function) fn_sig
       (@Errors.OK _)
       (function_lsim mrelT_ops)
       prog_src prog_tgt).

Variable (mrel_init:mrelT). (* TODO *)

Inductive match_stackframes: forall (height:nat) (mrel:mrelT) (cs_src cs_tgt:list stackframe), Prop :=
| match_stackframes_nil:
    match_stackframes 0 mrel_init nil nil
| match_stackframes_cons
    height ps_src ps_tgt s_src s_tgt
    emrel mrel
    (Hp: match_stackframes height emrel ps_src ps_tgt)
    (Hmrel_le: mrelT_ops.(le) emrel mrel)
    (Hreturn:
       forall rmrel ri st_src st_tgt mem_src mem_tgt vres_src vres_tgt
              (Hvres: mrelT_ops.(sem_value) rmrel vres_src vres_tgt)
              (Hst_src: st_src = Returnstate s_src vres_src mem_src)
              (Hst_tgt: st_tgt = Returnstate s_tgt vres_tgt mem_tgt)
              (Hsound_src: sound_state_ext prog_src st_src)
              (Hsound_tgt: sound_state_ext prog_tgt st_tgt)
              (Hrmrel_le: mrelT_ops.(le_public) mrel rmrel)
              (Hst_mem: mrelT_ops.(sem) rmrel prog_src prog_tgt ri st_src st_tgt),
         state_lsim mrelT_ops prog_src prog_tgt ps_src ps_tgt emrel rmrel ri st_src st_tgt):
    match_stackframes (S height) mrel s_src s_tgt
.

Inductive match_states (i:WF.t) (st_src st_tgt:state): Prop :=
| match_states_intro
    height ps_src ps_tgt
    emrel mrel
    (Hp: match_stackframes height emrel ps_src ps_tgt)
    (Hmrel_le: mrelT_ops.(le) emrel mrel)
    (Hsim: state_lsim mrelT_ops prog_src prog_tgt ps_src ps_tgt emrel mrel i st_src st_tgt)
.

Lemma program_sim_forward_simulation:
  forward_simulation (semantics prog_src) (semantics prog_tgt).
Proof.
  eapply (Forward_simulation
            (semantics prog_src)
            (semantics prog_tgt)
            WF.wf
            match_states).
  { (* initial *)
    intros. inversion H. 
    exploit funct_ptr_translated; eauto. intros [tf [A B]].
    exists WF.elt. exists (Callstate nil tf nil m0); split.
    - econstructor; eauto.
      eapply program_lsim_init_mem_match; eauto.
      replace (prog_main prog_tgt) with (prog_main prog_src).
      erewrite symbols_preserved; eauto; auto.
      destruct Hsim as [_ Hmain]. auto.
      rewrite <- H3. inv B. inv Hsig.
      destruct f, tf; auto.
    - econstructor.
      { apply match_stackframes_nil. }
      { instantiate (1 := mrel_init).
        destruct mrelT_props. reflexivity.
      }
      exploit funct_ptr_translated'; eauto.
      intros [tf' [Htf' Hfundef_sim]]. rewrite A in Htf'. symmetry in Htf'. inv Htf'.
      inv Hfundef_sim; destruct f, tf; inv Hsrc; inv Htgt.
      + exploit Hsim0; try reflexivity. unfold F_future_lsim. intros.
        destruct H4 as [Hfunction_sim Hfunction_sig].
        exploit Hfunction_sim.
        { eapply program_lsim_aux_le; eauto. }
        intro X. inv X. eapply Hlsim; eauto.
        * instantiate (1 := mrel_init).
          destruct mrelT_props. reflexivity.
        * admit. (* mrel_init *)
        * constructor.
        * apply sound_initial. auto.
        * apply sound_initial.
          admit. (* initial_state (hard) *)
      + admit. (* if external function is main? (hard) *)
  }
  { (* final *)
    simpl. intros. inv H0. inv H. punfold Hsim0. inv Hsim0.
    - inv Hst_src. auto.
    - inv Hst_src.
      revert height emrel Hmrel_le Hmrel_le_public Hp.
      refine (strong_nat_ind _ _). intros height IHheight emrel Hmrel_le Hmrel_le_public Hp.
      inversion Hp; symmetry in H0; subst.
      { exploit (mrelT_props.(sem_value_int)); eauto. intro. subst.
        constructor.
      }
      { exploit Hreturn; eauto. intro Hsim'.
        punfold Hsim'. inv Hsim'.
        { inv Hst_src. inv Hst_tgt. constructor. }
        { inv Hst_src. inv Hst_tgt.
          assert (Hle: mrelT_ops.(le) emrel0 mrel).
          { destruct mrelT_props. etransitivity; eauto. }
          eauto.
        }
        { exfalso. eapply Hnfinal. constructor. }
      }
    - exfalso. eapply Hnfinal. constructor.
  }
  { (* progress & preservation *)
    intros. inv H0.
    revert height i s2 ps_src ps_tgt emrel mrel Hp Hmrel_le Hsim0.
    refine (strong_nat_ind _ _). intros height IHheight. intros.
    punfold Hsim0. inv Hsim0.
    - (* term *)
      inv Hst_src. inv H.
    - (* return *)
      inversion Hp; symmetry in H1; subst; inv H.
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
        instantiate (1 := stack_tgt). instantiate (1 := stack_src). intros. subst.
        exploit Hreturn; eauto. intro Hsim2. pclearbot. eauto.
      }
      { destruct mrelT_props. reflexivity. }
      inv Hfundef. exploit funct_ptr_translated'; eauto.
      intros [tf [Htf Hfundef_sim]]. unfold Genv.find_funct_ptr in Htf.
      unfold fundef in *. rewrite Htgt in Htf. symmetry in Htf. inv Htf.
      inv Hfundef_sim; destruct fundef_src, fundef_tgt; inv Hsrc0; inv Htgt0.
      + exploit Hsim0; try reflexivity. unfold F_future_lsim. intros.
        destruct H0 as [Hfunction_sim Hfunction_sig].
        exploit Hfunction_sim.
        { eapply program_lsim_aux_le; eauto. }
        intro X. inv X. eapply Hlsim; eauto.
        { eapply sound_past_step; eauto. }
        destruct Hstep2 as [Hstep2|[Hstep2 _]].
        * eapply sound_past_plus; eauto.
        * eapply sound_past_star; eauto.
      + pfold. constructor.
        { intros ? Hfinal. inv Hfinal. }
        { eapply sound_past_step; eauto. }
        { destruct Hstep2 as [Hstep2|[Hstep2 _]].
          - eapply sound_past_plus; eauto.
          - eapply sound_past_star; eauto.
        }
        intros.
        admit. (* external function (hard) *)
  }
  { eapply symbols_preserved; eauto. }
Qed.

End GLOBAL_SIM.
