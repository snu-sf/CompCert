Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_linker.
Require Import Maps Maps_linker.
Require Import Integers Floats Values AST Globalenvs.
Require Import Language Linker LinkerProp Linkeq.
Require Import Errors.
Require Import paco.

Set Implicit Arguments.

(* external function prservation function *)
Lemma external_function_OK_sig:
  forall ef1 ef2, (OK ef1 = OK ef2) -> ef_sig ef1 = ef_sig ef2.
Proof.
  intros. inv H. auto.
Qed.

(* lifting function simulation to program simulation *)
Section PROGRAM_LSIM.

Variable (lang_src lang_tgt:Language).
  
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
Variable (transf_efT: forall (ef:efT_src), res efT_tgt).
Variable (transf_vT: forall (v:vT_src), res vT_tgt).
Hypothesis transf_efT_sigT: forall ef_src ef_tgt (H: transf_efT ef_src = OK ef_tgt), transf_sigT (ef_sig_src ef_src) = ef_sig_tgt ef_tgt.

Let sig_lsim (sig_src:sigT_src) (sig_tgt:sigT_tgt) := transf_sigT sig_src = sig_tgt.
Let ef_lsim (ef_src:efT_src) (ef_tgt:efT_tgt) := transf_efT ef_src = OK ef_tgt.
Let v_lsim (v_src:vT_src) (v_tgt:vT_tgt) := transf_vT v_src = OK v_tgt.

Definition f_lsimT :=
  forall
    (fprog_src:lang_src.(progT)) (fprog_tgt:lang_tgt.(progT))
    (f_src:fT_src) (f_tgt:fT_tgt), Prop.

Ltac clarify :=
  unfold fd_sig_src, fd_sig_tgt, Fundef_sig, f_sig_src, f_sig_tgt, ef_sig_src, ef_sig_tgt in *;
  unfold fundefT_src, vT_src, fundefT_tgt, vT_tgt, fundef_dec_src, fundef_dec_tgt in *;
  unfold fT_src, fT_tgt, efT_src, efT_tgt in *;
  repeat
    (try match goal with
           | [H1: Fundef_dec ?fundefT ?f = _, H2: Fundef_dec ?fundefT ?f = _ |- _] =>
             rewrite H1 in H2; inv H2
           | [H: match ?x with | inl _ => False | inr _ => _ end |- _] =>
             let Hx := fresh "Hx" in destruct x eqn:Hx; [inv H|]
           | [H: match ?x with | inr _ => False | inl _ => _ end |- _] =>
             let Hx := fresh "Hx" in destruct x eqn:Hx; [|inv H]
           | [H: False |- _] => inv H
         end;
     auto).

Section CORE.

Variable (f_lsim:f_lsimT).
Variable (prog_src:lang_src.(progT)).
Variable (prog_tgt:lang_tgt.(progT)).

Inductive globvar_lsim (v_src:globvar vT_src) (v_tgt:globvar vT_tgt): Prop :=
| globvar_lsim_intro
    (Hv: transf_globvar transf_vT v_src = OK v_tgt)
.

(** simulation *)
Inductive globfun_lsim
          (g_src:fundefT_src) (g_tgt:fundefT_tgt): Prop :=
| globfun_lsim_intro
    (Hsim:
       match fundef_dec_src g_src, fundef_dec_tgt g_tgt with
         | inl f_src, inl f_tgt =>
           forall fprog_src fprog_tgt
                  (Hfprog_src: program_linkeq lang_src prog_src fprog_src)
                  (Hfprog_tgt: program_linkeq lang_tgt prog_tgt fprog_tgt),
             f_lsim fprog_src fprog_tgt f_src f_tgt /\
             sig_lsim (f_sig_src f_src) (f_sig_tgt f_tgt)
         | inr ef_src, inr ef_tgt =>
           ef_lsim ef_src ef_tgt
         | _, _ => False
       end).

Inductive globdef_lsim:
  forall (g_src:globdef fundefT_src vT_src) (g_tgt:globdef fundefT_tgt vT_tgt), Prop :=
| globdef_lsim_fun
    f_src f_tgt (Hf: globfun_lsim f_src f_tgt):
    globdef_lsim (Gfun f_src) (Gfun f_tgt)
| globdef_lsim_var
    v_src v_tgt (Hv: globvar_lsim v_src v_tgt):
    globdef_lsim (Gvar v_src) (Gvar v_tgt)
.

Definition globdefs_lsim
           (defs_src:PTree.t (globdef fundefT_src vT_src))
           (defs_tgt:PTree.t (globdef fundefT_tgt vT_tgt)): Prop :=
  forall i,
    match PTree.get i defs_src, PTree.get i defs_tgt with
      | Some g1, Some g2 => globdef_lsim g1 g2
      | None, None => True
      | _, _ => False
    end.

Definition globdef_list_lsim
           (defs_src:list (positive * globdef fundefT_src vT_src))
           (defs_tgt:list (positive * globdef fundefT_tgt vT_tgt)): Prop :=
  list_forall2
    (fun g_src g_tgt =>
       fst g_src = fst g_tgt /\
       globdef_lsim (snd g_src) (snd g_tgt))
    defs_src defs_tgt.

Definition program_lsim_aux: Prop :=
  globdef_list_lsim prog_src.(prog_defs) prog_tgt.(prog_defs) /\
  prog_src.(prog_main) = prog_tgt.(prog_main).

End CORE.

(** an instantiation of weak simulation: matching any function definitions *)
Definition program_weak_lsim := program_lsim_aux (fun _ _ _ _ => True).

(** properties on f_lsim and simulation *)
Lemma globfun_lsim_le
      (f_lsim1 f_lsim2:f_lsimT)
      (prog1_src prog2_src:program fundefT_src vT_src)
      (prog1_tgt prog2_tgt:program fundefT_tgt vT_tgt)
      (Hf_lsim: f_lsim1 <4= f_lsim2)
      (Hprog_src: program_linkeq lang_src prog1_src prog2_src)
      (Hprog_tgt: program_linkeq lang_tgt prog1_tgt prog2_tgt):
  (globfun_lsim f_lsim1 prog1_src prog1_tgt) <2= (globfun_lsim f_lsim2 prog2_src prog2_tgt).
Proof.
  intros. inv PR; constructor.
  destruct (fundef_dec_src x0), (fundef_dec_tgt x1); auto.
  intros. exploit Hsim; eauto. intros [Hsim1 Hsig].
  split; auto. apply Hf_lsim. eapply Hsim.
  + rewrite Hprog_src. auto.
  + rewrite Hprog_tgt. auto.
Qed.

Lemma globdef_lsim_le
      (f_lsim1 f_lsim2:f_lsimT)
      (prog1_src prog2_src:program fundefT_src vT_src)
      (prog1_tgt prog2_tgt:program fundefT_tgt vT_tgt)
      (Hf_lsim: f_lsim1 <4= f_lsim2)
      (Hprog_src: program_linkeq lang_src prog1_src prog2_src)
      (Hprog_tgt: program_linkeq lang_tgt prog1_tgt prog2_tgt):
  (globdef_lsim f_lsim1 prog1_src prog1_tgt) <2= (globdef_lsim f_lsim2 prog2_src prog2_tgt).
Proof.
  intros. inv PR.
  - eapply globdef_lsim_fun; eauto.
    eapply globfun_lsim_le; eauto.
  - eapply globdef_lsim_var; eauto.
Qed.

Lemma globdef_list_lsim_le
      (f_lsim1 f_lsim2:f_lsimT)
      (prog1_src prog2_src:program fundefT_src vT_src)
      (prog1_tgt prog2_tgt:program fundefT_tgt vT_tgt)
      (Hf_lsim: f_lsim1 <4= f_lsim2)
      (Hprog_src: program_linkeq lang_src prog1_src prog2_src)
      (Hprog_tgt: program_linkeq lang_tgt prog1_tgt prog2_tgt):
  (globdef_list_lsim f_lsim1 prog1_src prog1_tgt) <2= (globdef_list_lsim f_lsim2 prog2_src prog2_tgt).
Proof.
  intros.
  eapply list_forall2_imply; eauto. simpl. intros.
  destruct H1, v1, v2. simpl in *. subst.
  split; auto. eapply globdef_lsim_le; eauto.
Qed.

Lemma program_lsim_aux_le
      (f_lsim1 f_lsim2:f_lsimT)
      (Hf_lsim: f_lsim1 <4= f_lsim2):
  (program_lsim_aux f_lsim1) <2= (program_lsim_aux f_lsim2).
Proof.
  intros prog_src prog_tgt Hsim.
  destruct prog_src as [defs_src main_src].
  destruct prog_tgt as [defs_tgt main_tgt].
  destruct Hsim as [Hdefs Hmain].
  simpl in *. subst. split; auto.
  eapply globdef_list_lsim_le; simpl; eauto.
  reflexivity. reflexivity.
Qed.

(** globdefs_lsim and globdef_list_lsim *)

Lemma globdefs_lsim_globdef_list_lsim
      (f_lsim:f_lsimT)
      (fprog_src:program fundefT_src vT_src)
      (fprog_tgt:program fundefT_tgt vT_tgt)
      (defs_src: PTree.t (globdef fundefT_src vT_src))
      (defs_tgt: PTree.t (globdef fundefT_tgt vT_tgt))
      (Hsim: globdefs_lsim f_lsim fprog_src fprog_tgt defs_src defs_tgt):
  globdef_list_lsim f_lsim fprog_src fprog_tgt (PTree.elements defs_src) (PTree.elements defs_tgt).
Proof.
  apply PTree.elements_canonical_order; intros.
  - exploit Hsim. instantiate (1 := i). rewrite H. intro X.
    destruct (defs_tgt ! i) eqn:Hi_tgt; [|inv X].
    eexists. split; eauto.
  - exploit Hsim. instantiate (1 := i). rewrite H. intro X.
    destruct (defs_src ! i) eqn:Hi_src; [|inv X].
    eexists. split; eauto.
Qed.

Lemma globdef_list_lsim_globdefs_lsim
      (f_lsim:f_lsimT)
      (fprog_src:program fundefT_src vT_src)
      (fprog_tgt:program fundefT_tgt vT_tgt)
      (defs_src: list (positive * (globdef fundefT_src vT_src)))
      (defs_tgt: list (positive * (globdef fundefT_tgt vT_tgt)))
      (Hsim: globdef_list_lsim f_lsim fprog_src fprog_tgt defs_src defs_tgt):
  globdefs_lsim f_lsim fprog_src fprog_tgt (PTree_unelements defs_src) (PTree_unelements defs_tgt).
Proof.
  unfold globdefs_lsim, globdef_list_lsim in *. intro i.
  rewrite ? PTree_guespec. apply list_forall2_rev in Hsim.
  revert Hsim i. generalize (rev defs_src) (rev defs_tgt).
  induction l; intros l0 Hsim i; inv Hsim; simpl; auto.
  destruct a, b1, H1. simpl in *. subst.
  destruct (peq i p0); simpl; subst; auto.
  apply IHl. auto.
Qed.

(** properties of linking on simulation *)

Lemma link_globdefs_lsim
      (f_lsim:f_lsimT)
      (main:positive)
      (defs1_src defs2_src:list (positive * globdef fundefT_src vT_src))
      (defs1_tgt defs2_tgt:list (positive * globdef fundefT_tgt vT_tgt))
      defs_src (Hdefs_src: link_globdefs lang_src (PTree_unelements defs1_src) (PTree_unelements defs2_src) = Some defs_src)
      (H1: globdefs_lsim
             f_lsim
             (mkprogram defs1_src main)
             (mkprogram defs1_tgt main)
             (PTree_unelements defs1_src)
             (PTree_unelements defs1_tgt))
      (H2: globdefs_lsim
             f_lsim
             (mkprogram defs2_src main)
             (mkprogram defs2_tgt main)
             (PTree_unelements defs2_src)
             (PTree_unelements defs2_tgt)):
  exists defs_tgt,
    link_globdefs lang_tgt (PTree_unelements defs1_tgt) (PTree_unelements defs2_tgt) = Some defs_tgt /\
    globdefs_lsim
      f_lsim
      (mkprogram (PTree.elements defs_src) main)
      (mkprogram (PTree.elements defs_tgt) main)
      defs_src defs_tgt.
Proof.
  generalize (link_globdefs_linkeq_l _ _ _ Hdefs_src). intro Hle1_src.
  generalize (link_globdefs_linkeq_r _ _ _ Hdefs_src). intro Hle2_src.
  destruct (link_globdefs lang_tgt (PTree_unelements defs1_tgt) (PTree_unelements defs2_tgt)) as [defs_tgt|] eqn:Hdefs_tgt.
  { generalize (link_globdefs_linkeq_l _ _ _ Hdefs_tgt). intro Hle1_tgt.
    generalize (link_globdefs_linkeq_r _ _ _ Hdefs_tgt). intro Hle2_tgt.
    eexists. split; [eauto|].
    intro i. 
    eapply gtlink_globdefs in Hdefs_src. instantiate (1 := i) in Hdefs_src.
    eapply gtlink_globdefs in Hdefs_tgt. instantiate (1 := i) in Hdefs_tgt.
    specialize (H1 i). specialize (H2 i). clarify.
    destruct ((PTree_unelements defs1_src) ! i) eqn:Hi1_src,
             ((PTree_unelements defs2_src) ! i) eqn:Hi2_src,
             (defs_src ! i) eqn:Hi_src; subst; try (inv Hdefs_src; fail);
    destruct ((PTree_unelements defs1_tgt) ! i) eqn:Hi1_tgt,
             ((PTree_unelements defs2_tgt) ! i) eqn:Hi2_tgt,
             (defs_tgt ! i) eqn:Hi_tgt; subst; try (inv Hdefs_tgt; fail);
    try (inv H1; fail); try (inv H2; fail); auto.
    { destruct Hdefs_src as [[]|[]], Hdefs_tgt as [[]|[]]; subst; clarify.
      - eapply globdef_lsim_le; eauto.
        + split; auto. unfold globdef_list_linkeq. rewrite Hle2_src.
          repeat intro. exists def1. split; [|reflexivity].
          simpl. rewrite PTree_unelements_elements. auto.
        + split; auto. unfold globdef_list_linkeq. rewrite Hle2_tgt.
          repeat intro. exists def1. split; [|reflexivity].
          simpl. rewrite PTree_unelements_elements. auto.
      - inv H; inv H1; inv H2; inv H3; inv Hv; inv Hv0; try inv Hf; try inv Hf0; clarify;
        repeat constructor; clarify;
        rewrite ? H1, ? H2, ? H0, ? H3 in *; clarify.
        inv Hv1. inv Hv2. unfold transf_globvar in *. rewrite Hinfo in *.
        clarify. destruct (transf_vT (gvar_info v2)); inv Hv; inv Hv0.
        simpl in *. f_equal. f_equal; auto. rewrite Hinit, Hinit0. auto.
      - inv H; inv H1; inv H2; inv H3; inv Hv; inv Hv0; try inv Hf; try inv Hf0; clarify;
        repeat constructor; clarify;
        rewrite ? H1, ? H2, ? H0, ? H3 in *; clarify.
        inv Hv1. inv Hv2. unfold transf_globvar in *. clarify. rewrite Hinfo in *.
        clarify. destruct (transf_vT (gvar_info v2)); inv Hv; inv Hv0.
        simpl in *. f_equal. f_equal; auto. rewrite Hinit, Hinit0. auto.
      - inv H; inv H1; inv H2; inv H3; inv Hv; inv Hv0; try inv Hf; try inv Hf0; clarify;
        repeat constructor; clarify;
        rewrite ? H1, ? H2, ? H0, ? H3 in *; clarify.
        intros. apply Hsim.
        + rewrite <- Hfprog_src. constructor; simpl; auto.
          unfold globdef_list_linkeq in *. repeat intro.
          rewrite PTree_unelements_elements. auto.
        + rewrite <- Hfprog_tgt. constructor; simpl; auto.
          unfold globdef_list_linkeq in *. repeat intro.
          rewrite PTree_unelements_elements. auto.
    }
    { eapply globdef_lsim_le; eauto.
      - split; auto. unfold globdef_list_linkeq. rewrite Hle1_src.
        repeat intro. exists def1. split; [|reflexivity].
        simpl. rewrite PTree_unelements_elements. auto.
      - split; auto. unfold globdef_list_linkeq. rewrite Hle1_tgt.
        repeat intro. exists def1. split; [|reflexivity].
        simpl. rewrite PTree_unelements_elements. auto.
    }
    { eapply globdef_lsim_le; eauto.
      - split; auto. unfold globdef_list_linkeq. rewrite Hle2_src.
        repeat intro. exists def1. split; [|reflexivity].
        simpl. rewrite PTree_unelements_elements. auto.
      - split; auto. unfold globdef_list_linkeq. rewrite Hle2_tgt.
        repeat intro. exists def1. split; [|reflexivity].
        simpl. rewrite PTree_unelements_elements. auto.
    }
  }
  { apply gflink_globdefs in Hdefs_tgt.
    destruct Hdefs_tgt as [i [def1 [def2 [Hdef1 [Hdef2 [H12 H21]]]]]].
    specialize (H1 i). clarify. rewrite Hdef1 in H1.
    destruct ((PTree_unelements defs1_src) ! i) eqn:Hi1_src; [|inv H1].
    specialize (H2 i). clarify. rewrite Hdef2 in H2.
    destruct ((PTree_unelements defs2_src) ! i) eqn:Hi2_src; [|inv H2].
    eapply gtlink_globdefs in Hdefs_src.
    instantiate (1 := i) in Hdefs_src.
    rewrite Hi1_src, Hi2_src in Hdefs_src.
    destruct (defs_src ! i) eqn:Hi_src; [|inv Hdefs_src].
    destruct Hdefs_src as [[]|[]]; subst.
    { inv H1; inv H2; inv H; inv Hv; try inv Hv0; try inv Hf; try inv Hf0; clarify;
      rewrite ? H0, ? H1, ? H2 in *; clarify.
      { contradict H12. constructor. eapply globfun_linkable_ei; eauto.
        exploit Hsim0; eauto; try reflexivity. intros [_ Hsig1]. inv Hsig1.
        inv Hsim. exploit transf_efT_sigT; eauto. intro X.
        clarify. rewrite <- X, Hsig, H0. auto.
      }
      { contradict H12. constructor. eapply globfun_linkable_ee; eauto.
        inv Hsim. inv Hsim0. rewrite H2 in H3. inv H3. auto.
      }
      { contradict H12. constructor.
        destruct v_src, v_src0. inv Hv1. simpl in *. subst.
        unfold transf_globvar in *. simpl in *.
        destruct (transf_vT gvar_info0); inv Hv; inv Hv2; simpl in *; subst.
        constructor; auto.
      }
    }
    { inv H1; inv H2; inv H; inv Hv; try inv Hv0; try inv Hf; try inv Hf0; clarify;
      rewrite ? H0, ? H1, ? H2 in *; clarify.
      { contradict H21. constructor. eapply globfun_linkable_ei; eauto.
        exploit Hsim; eauto; try reflexivity. intros [_ Hsig1]. inv Hsig1.
        inv Hsim0. exploit transf_efT_sigT; eauto. intro X.
        clarify. rewrite <- X, Hsig, H0. auto.
      }
      { contradict H21. constructor. eapply globfun_linkable_ee; eauto.
        inv Hsim. inv Hsim0. rewrite H2 in H3. inv H3. auto.
      }
      { contradict H21. constructor.
        destruct v_src, v_src0. inv Hv1. simpl in *. subst.
        unfold transf_globvar in *. simpl in *.
        destruct (transf_vT gvar_info); inv Hv; inv Hv2; simpl in *; subst.
        constructor; auto.
      }
    }
  }
Qed.

Lemma link_globdef_list_lsim
      (f_lsim:f_lsimT)
      (main:positive)
      (defs1_src defs2_src:list (positive * globdef fundefT_src vT_src))
      (defs1_tgt defs2_tgt:list (positive * globdef fundefT_tgt vT_tgt))
      defs_src (Hdefs_src: link_globdef_list lang_src defs1_src defs2_src = Some defs_src)
      (H1: globdef_list_lsim
             f_lsim
             (mkprogram defs1_src main)
             (mkprogram defs1_tgt main)
             defs1_src defs1_tgt)
      (H2: globdef_list_lsim
             f_lsim
             (mkprogram defs2_src main)
             (mkprogram defs2_tgt main)
             defs2_src defs2_tgt):
  exists defs_tgt,
    link_globdef_list lang_tgt defs1_tgt defs2_tgt = Some defs_tgt /\
    globdef_list_lsim
      f_lsim
      (mkprogram defs_src main)
      (mkprogram defs_tgt main)
      defs_src defs_tgt.
Proof.
  apply globdef_list_lsim_globdefs_lsim in H1.
  apply globdef_list_lsim_globdefs_lsim in H2.
  unfold link_globdef_list in Hdefs_src.
  match goal with
    | [H: context[link_globdefs ?lang ?defs1 ?defs2] |- _] =>
      destruct (link_globdefs lang defs1 defs2) as [defs|] eqn:Hdefs; inv H
  end.
  exploit link_globdefs_lsim; eauto. intros [defs_tgt [Hdefs_tgt Hsim]].
  unfold link_globdef_list. clarify. rewrite Hdefs_tgt. eexists. split; eauto.
  apply globdefs_lsim_globdef_list_lsim. auto.
Qed.

Section DEF.

Variable (f_lsim:f_lsimT).

Definition F_future_lsim :=
  fun fprog_src fprog_tgt f_src f_tgt =>
    forall (Hfprog: program_weak_lsim fprog_src fprog_tgt),
    f_lsim fprog_src fprog_tgt f_src f_tgt.

Definition program_lsim
           (prog_src: program fundefT_src vT_src)
           (prog_tgt: program fundefT_tgt vT_tgt): Prop :=
  globdef_list_lsim F_future_lsim prog_src prog_tgt prog_src.(prog_defs) prog_tgt.(prog_defs) /\
  prog_src.(prog_main) = prog_tgt.(prog_main).

Lemma link_program_lsim
      (p1_src p2_src:program fundefT_src vT_src)
      (p1_tgt p2_tgt:program fundefT_tgt vT_tgt)
      p_src (Hp_src: link_program lang_src p1_src p2_src = Some p_src)
      (H1: program_lsim p1_src p1_tgt)
      (H2: program_lsim p2_src p2_tgt):
  exists p_tgt,
    link_program lang_tgt p1_tgt p2_tgt = Some p_tgt /\
    program_lsim p_src p_tgt.
Proof.
  destruct p1_src as [defs1_src main1_src].
  destruct p1_tgt as [defs1_tgt main1_tgt].
  destruct p2_src as [defs2_src main2_src].
  destruct p2_tgt as [defs2_tgt main2_tgt].
  destruct H1 as [H1d H1m], H2 as [H2d H2m].
  unfold link_program in *. simpl in *. subst.
  destruct ((main1_tgt =? main2_tgt)%positive) eqn:Hmain; [|inv Hp_src].
  apply Pos.eqb_eq in Hmain. subst.
  destruct (link_globdef_list lang_src defs1_src defs2_src) as [def_list_src|] eqn:Hdef_list_src; inv Hp_src.
  exploit link_globdef_list_lsim; eauto. intros [defs_tgt [Hdefs_tgt Hsim]].
  exists (mkprogram defs_tgt main2_tgt). rewrite Hdefs_tgt. split; auto.
  constructor; auto.
Qed.

End DEF.

Lemma program_lsim_le
      (f_lsim1 f_lsim2:f_lsimT) (Hf_lsim: f_lsim1 <4= f_lsim2):
  (program_lsim f_lsim1) <2= (program_lsim f_lsim2).
Proof.
  intros. destruct PR as [Hdefs Hmain]. split; auto.
  eapply globdef_list_lsim_le; eauto.
  - reflexivity.
  - reflexivity.
  - eapply list_forall2_imply; eauto. intros. simpl in *.
    destruct v1, v2, H1. simpl in *. subst.
    split; auto.
    eapply globdef_lsim_le; try reflexivity; [|eauto].
    intros. repeat intro. specialize (PR Hfprog). auto.
Qed.

Inductive fundef_sig_lsim (f_src:fundefT_src) (f_tgt:fundefT_tgt): Prop :=
| fundef_sig_lsim_intro
    (Hsig: sig_lsim (fd_sig_src f_src) (fd_sig_tgt f_tgt))
.

Inductive fundef_weak_lsim
          (ge_src:Genv.t fundefT_src vT_src) (ge_tgt:Genv.t fundefT_tgt vT_tgt)
          (f_src:fundefT_src) (f_tgt:fundefT_tgt): Prop :=
| fundef_weak_lsim_intro
    (Hsig: fundef_sig_lsim f_src f_tgt)
    b
    (Hsrc: Maps.PTree.get b ge_src.(Genv.genv_funs) = Some f_src)
    (Htgt: Maps.PTree.get b ge_tgt.(Genv.genv_funs) = Some f_tgt)
.

Section INITIALIZE.

Variable (fprog_src: program fundefT_src vT_src).
Variable (fprog_tgt: program fundefT_tgt vT_tgt).
Variable (f_lsim:f_lsimT).
Variable (Hfprog: program_lsim_aux f_lsim fprog_src fprog_tgt).

Inductive match_fundef (f_src:fundefT_src) (f_tgt:fundefT_tgt): Prop :=
| match_fundef_intro
    (Hsig: fundef_sig_lsim f_src f_tgt)
    (Hsim: globfun_lsim f_lsim fprog_src fprog_tgt f_src f_tgt)
.

Let ge_src := Genv.globalenv fprog_src.
Let ge_tgt := Genv.globalenv fprog_tgt.

Lemma program_lsim_match_program:
  match_program match_fundef v_lsim nil fprog_src.(prog_main) fprog_src fprog_tgt.
Proof.
  unfold match_program. destruct Hfprog as [Hfdefs Hmain].
  split; eauto. exists fprog_tgt.(prog_defs). split; [|rewrite app_nil_r; auto].
  revert Hfdefs. clarify. generalize (prog_defs fprog_src) as l1, (prog_defs fprog_tgt) as l2.
  induction l1; intros l2 Hsim; inv Hsim; constructor; auto.
  destruct a, b1, H1. simpl in *. subst.
  inv H0.
  - inv Hf. clarify.
    destruct (Fundef_dec (fundefT lang_src) f_src) eqn:Hsrc,
             (Fundef_dec (fundefT lang_tgt) f_tgt) eqn:Htgt; try (inv Hsim; fail).
    + exploit Hsim; try reflexivity. intros [_ ?].
      repeat constructor; clarify; rewrite Hsrc, Htgt; auto.
    + repeat constructor; clarify; rewrite Hsrc, Htgt; auto.
      apply transf_efT_sigT. auto.
  - destruct v_src, v_tgt. inv Hv. unfold transf_globvar in Hv0. simpl in *.
    destruct (transf_vT gvar_info) eqn:Hgvar_info; inv Hv0. constructor; auto.
Qed.
Local Hint Resolve program_lsim_match_program.

Lemma globalenvs_match:
  Genv.match_genvs match_fundef v_lsim nil (Genv.globalenv fprog_src) (Genv.globalenv fprog_tgt).
Proof. eapply Genv.globalenvs_match; eauto. Qed.
Local Hint Resolve globalenvs_match.

Lemma program_lsim_init_mem_match:
  forall m,
    Genv.init_mem fprog_src = Some m ->
    Genv.init_mem fprog_tgt = Some m.
Proof.
  intros. erewrite Genv.init_mem_match; eauto; auto.
Qed.

Lemma symbols_preserved:
  forall (s : ident),
  Genv.find_symbol (Genv.globalenv fprog_tgt) s = Genv.find_symbol (Genv.globalenv fprog_src) s.
Proof.
  intros. eapply Genv.find_symbol_match; eauto.
Qed.

Lemma varinfo_preserved:
  forall b,
    match Genv.find_var_info (Genv.globalenv fprog_tgt) b, Genv.find_var_info (Genv.globalenv fprog_src) b with
      | None, None => True
      | Some v_tgt, Some v_src =>
        transf_globvar transf_vT v_src = OK v_tgt
      | _, _ => False
    end.
Proof.
  intros. case_eq (Genv.find_var_info (Genv.globalenv fprog_src) b); intros.
  - exploit Genv.find_var_info_match; eauto. intros [tv [Htv Hsim]].
    rewrite Htv. inv Hsim. inv H0.
    unfold transf_globvar, bind. simpl in *. rewrite H2. auto.
  - case_eq (Genv.find_var_info (Genv.globalenv fprog_tgt) b); intros; auto.
    exploit Genv.find_var_info_rev_match; eauto.
    destruct (plt b (Genv.genv_next (Genv.globalenv fprog_src))); [|intro X; inv X].
    intros [v [Hv Hsim]]. rewrite H in Hv. inv Hv.
Qed.

Lemma block_is_volatile_preserved:
  forall b, Events.block_is_volatile ge_tgt b = Events.block_is_volatile ge_src b.
Proof.
  intros. unfold Events.block_is_volatile. generalize (varinfo_preserved b).
  unfold ge_src, ge_tgt.
  destruct (Genv.find_var_info (Genv.globalenv fprog_src) b),
           (Genv.find_var_info (Genv.globalenv fprog_tgt) b); intro X; inv X; auto.
  unfold transf_globvar in H0. destruct (transf_vT (gvar_info g)); inv H0; auto.
Qed.

Lemma funct_ptr_translated:
  forall (b : block) (f : fundefT_src),
  Genv.find_funct_ptr (Genv.globalenv fprog_src) b = Some f ->
  exists tf : fundefT_tgt,
  Genv.find_funct_ptr (Genv.globalenv fprog_tgt) b = Some tf /\ fundef_weak_lsim ge_src ge_tgt f tf.
Proof.
  intros. exploit Genv.find_funct_ptr_match; eauto. intros [tf [Htf Hsim]].
  eexists. split; eauto. inv Hsim. inv Hsig. unfold Genv.find_funct_ptr in *.
  repeat econstructor; eauto.
Qed.

Lemma funct_ptr_translated':
  forall (b : block) (f : fundefT_src),
  Genv.find_funct_ptr (Genv.globalenv fprog_src) b = Some f ->
  exists tf : fundefT_tgt,
  Genv.find_funct_ptr (Genv.globalenv fprog_tgt) b = Some tf /\ globfun_lsim f_lsim fprog_src fprog_tgt f tf.
Proof.
  intros. exploit Genv.find_funct_ptr_match; eauto. intros [tf [Htf Hsim]].
  exists tf. split; auto. inv Hsim. auto.
Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct (Genv.globalenv fprog_src) v = Some f ->
  exists tf, Genv.find_funct (Genv.globalenv fprog_tgt) v = Some tf /\ fundef_weak_lsim ge_src ge_tgt f tf.
Proof.
  intros. destruct v; inv H. 
  destruct (Int.eq_dec i Int.zero); inv H1.
  apply funct_ptr_translated. auto.
Qed.

Lemma sig_preserved:
  forall f tf (Hsim: fundef_sig_lsim f tf),
    sig_lsim (fd_sig_src f) (fd_sig_tgt tf).
Proof.
  intros. inv Hsim. auto.
Qed.

End INITIALIZE.

End PROGRAM_LSIM.
