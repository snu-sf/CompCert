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
Require Import Csyntax Csem Clight.
Require Import LinkerSpecification.
Require Import ProgramLSim SimplExprLSim.

Set Implicit Arguments.

Section GLOBAL_SIM.

Variable (mrelT:Type).
Variable (mrelT_ops:mrelT_opsT mrelT).
Hypothesis (mrelT_props:mrelT_propsT mrelT_ops).

Variable (prog_src:Csyntax.program).
Variable (prog_tgt:program).

Hypothesis
  (Hsim:
     program_lsim
       C_fundef_dec signature_of_C_function
       Clight_fundef_dec Cshmgen.signature_of_function
       transf_V
       (function_lsim mrelT_ops)
       prog_src prog_tgt).

Lemma Hweak_sim:
  program_weak_lsim
    C_fundef_dec signature_of_C_function
    Clight_fundef_dec Cshmgen.signature_of_function
    transf_V
    prog_src prog_tgt.
Proof. eapply program_lsim_aux_le; eauto. Qed.
Hint Resolve Hweak_sim.

Inductive match_stackframes: forall (height:nat) (mrel:mrelT) (cs_src:Csem.cont) (cs_tgt:Clight.cont), Prop :=
| match_stackframes_nil mrel_init:
    match_stackframes 0 mrel_init Csem.Kstop Clight.Kstop
| match_stackframes_cons
    height ps_src ps_tgt s_src s_tgt
    emrel mrel
    (Hp: match_stackframes height emrel ps_src ps_tgt)
    (Hmrel_le: mrelT_ops.(le) emrel mrel)
    (Hreturn:
       forall rmrel ri st_src st_tgt mem_src mem_tgt vres_src vres_tgt
              (Hvres: mrelT_ops.(sem_value) rmrel vres_src vres_tgt)
              (Hst_src: st_src = Csem.Returnstate vres_src s_src mem_src)
              (Hst_tgt: st_tgt = Clight.Returnstate vres_tgt s_tgt mem_tgt)
              (Hrmrel_le: mrelT_ops.(le_public) mrel rmrel)
              (Hst_mem: mrelT_ops.(sem) rmrel prog_src prog_tgt ri st_src st_tgt),
         state_lsim mrelT_ops prog_src prog_tgt ps_src ps_tgt emrel rmrel ri st_src st_tgt):
    match_stackframes (S height) mrel s_src s_tgt
.

Inductive match_states (i:WF.t) (st_src:Csem.state) (st_tgt:Clight.state): Prop :=
| match_states_intro
    height ps_src ps_tgt
    emrel mrel
    (Hp: match_stackframes height emrel ps_src ps_tgt)
    (Hmrel_le: mrelT_ops.(le) emrel mrel)
    (Hsim: state_lsim mrelT_ops prog_src prog_tgt ps_src ps_tgt emrel mrel i st_src st_tgt)
.

Lemma program_sim_forward_simulation:
  forward_simulation (Csem.semantics prog_src) (Clight.semantics1 prog_tgt).
Proof.
  eapply (Forward_simulation
            (Csem.semantics prog_src)
            (Clight.semantics1 prog_tgt)
            WF.wf
            match_states).
  { (* initial *)
    intros. inversion H. 
    exploit funct_ptr_translated; eauto.
    intros [tf [A B]].
    assert (Hinitial_tgt: initial_state prog_tgt (Clight.Callstate tf nil Clight.Kstop m0)).
    { simpl. econstructor; eauto.
      eapply program_lsim_init_mem_match; eauto.
      replace (prog_main prog_tgt) with (prog_main prog_src).
      erewrite symbols_preserved; eauto.
      destruct Hsim as [_ Hmain]. auto.
      rewrite <- H3. inv B. inv Hsig.
      admit. (* signature *)
    }
    exploit (mrelT_props.(Hmrel_i_init)); eauto.
    intros [mrel_init [i_init Hinitial]].
    exists i_init. exists (Callstate tf nil Clight.Kstop m0). split; auto.
    econstructor.
    { apply match_stackframes_nil. }
    { destruct mrelT_props. reflexivity. }
    exploit funct_ptr_translated'; eauto.
    intros [tf' [Htf' Hfundef_sim]]. rewrite A in Htf'. symmetry in Htf'. inv Htf'.
    inv Hfundef_sim; destruct f, tf; inv Hsrc; inv Htgt.
    - exploit Hsim0; try reflexivity. unfold F_future_lsim. intros.
      destruct H4 as [Hfunction_sim Hfunction_sig].
      exploit Hfunction_sim; eauto.
      intro X. inv X. eapply Hlsim; eauto.
      constructor.
    - pfold. constructor.
      { intros r Hr. inv Hr. }
      intros. inversion Hst2_src; inv H4. subst.
      exploit (mrelT_props.(Hexternal_call)); eauto.
      { constructor. }
      intros [mrel2 [i2 [s2 [res2 [m2' [Hs2 [Hs2_step [Hmrel2 [Hmrel2_val Hmrel2_le]]]]]]]]].
      exists i2. exists s2. exists mrel2.
      split; [left; apply plus_one; auto|].
      split; [apply mrelT_props.(le_public_le); auto|].
      split; auto. inversion Hs2. subst.
      apply _state_lsim_or_csim_lsim. left. pfold.
      eapply _state_lsim_return; eauto.
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
      inv Hst_src. inv H; inv H0.
    - (* return *)
      inversion Hp; symmetry in H1; subst; inv H; inv H0.
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
      rewrite Htgt in Htf. symmetry in Htf. inv Htf.
      inv Hfundef_sim; destruct fundef_src, fundef_tgt; inv Hsrc0; inv Htgt0.
      + exploit Hsim0; try reflexivity. unfold F_future_lsim. intros.
        destruct H0 as [Hfunction_sim Hfunction_sig].
        exploit Hfunction_sim; eauto.
        intro X. inv X. eapply Hlsim; eauto.
      + pfold. constructor.
        { intros ? Hfinal. inv Hfinal. }
        intros. inversion Hst2_src; inv H0. subst.
        exploit (mrelT_props.(Hexternal_call)); eauto.
        intros [mrel3 [i3 [s3 [res3 [m3' [Hs3 [Hs3_step [Hmrel3 [Hmrel3_val Hmrel3_le]]]]]]]]].
        exists i3. exists s3. exists mrel3.
        split; [left; apply plus_one; auto|].
        split; [apply mrelT_props.(le_public_le); auto|].
        split; auto. inversion Hs3. subst.
        apply _state_lsim_or_csim_lsim. left. pfold.
        eapply _state_lsim_return; eauto.
  }
  { eapply symbols_preserved; eauto. }
Qed.

End GLOBAL_SIM.
